package org.example

import org.example.AstNode.ContextKey
import org.example.output.CompilerMessagePrinter
import org.example.verification.*
import java.lang.NumberFormatException

class LanguageResolver(private val input: String) {
    private val symbolMap = ScopeStack()
    private val compilerMessagePrinter = CompilerMessagePrinter(input)
    private var logicContainer = LogicContainer(compilerMessagePrinter)
    private var currentFunction: ResolvedSymbol.Function? = null

    private inline fun withLogicContainer(newContainer: LogicContainer, block: () -> Unit): LogicContainer {
        val oldContainer = logicContainer
        try {
            logicContainer = newContainer
            block()
            return logicContainer
        } finally {
            logicContainer = oldContainer
        }
    }

    private fun resolveType(node: TypeExprNode): ResolvedType? {
        return when (node) {
            is TypeNameNode -> when (node.name) {
                "int" -> IntType
                "bool" -> BoolType
                else -> {
                    compilerMessagePrinter.printError(node.offset, "Unknown type: '${node.name}'", "here")
                    null
                }
            }
        }
    }

    private fun resolveInvocation(node: InvocationNode): ResolvedType? {
        resolveExpr(node.expr)
        val symbol = node.expr[ResolvedSymbol.key] ?: return null
        if (symbol !is ResolvedSymbol.Callable) {
            compilerMessagePrinter.printError(node.expr.offset, "Symbol '${symbol.name}' is not callable", "here")
            return null
        }

        if (node.arguments.size != symbol.arguments.size) {
            compilerMessagePrinter.printError(node.offset, "Wrong number of arguments: expected " +
                    "${symbol.arguments.size}, found ${node.arguments.size}", "here")
            return null
        }

        for (i in node.arguments.indices) {
            val type = resolveExpr(node.arguments[i]) ?: return null
            val expectedType = symbol.arguments[i].type
            if (type != expectedType) {
                printErrorTypeMismatch(node.arguments[i].offset, expectedType, type, "in argument ${symbol.arguments[i].name}")
                return null
            }
        }

        // TODO should verify that input contract is true; already done in LogicContainer, should be moved here for all types of invocations
        symbol.contract?.output?.let { outputContract ->
            // TODO contract output should be resolved in resolveFunction, but I don't know how to deal with let-equals
            val argumentsMap = mutableMapOf<String, ExprNode>()
            for (i in node.arguments.indices) {
                argumentsMap[symbol.arguments[i].name] = node.arguments[i]
            }
            val proofElementList = replaceContractOutputPattern(outputContract, node, argumentsMap)
            logicContainer.verifyProofAndCollect(proofElementList, skipVerification = true)
        }

        return symbol.returnType
    }

    private fun resolveArithmetic(node: ArithmeticNode): ResolvedType {
        resolveExpr(node.left)
        resolveExpr(node.right)
        // TODO check left and right types
        return IntType
    }

    private fun resolveCompare(node: CompareNode): ResolvedType {
        resolveExpr(node.left)
        resolveExpr(node.right)
        // TODO check left and right types
        return BoolType
    }

    private fun resolveAnd(node: AndNode): ResolvedType? {
        assertType(resolveExpr(node.left), BoolType, node.left.offset) ?: return null
        assertType(resolveExpr(node.right), BoolType, node.right.offset) ?: return null
        return BoolType
    }

    private fun resolveOr(node: OrNode): ResolvedType? {
        assertType(resolveExpr(node.left), BoolType, node.left.offset) ?: return null
        assertType(resolveExpr(node.right), BoolType, node.right.offset) ?: return null
        return BoolType
    }

    private fun resolveArrow(node: ArrowNode): ResolvedType? {
        assertType(resolveExpr(node.left), BoolType, node.left.offset) ?: return null
        assertType(resolveExpr(node.right), BoolType, node.right.offset) ?: return null
        return BoolType
    }

    private fun resolveNot(node: NotNode): ResolvedType? {
        val exprType = resolveExpr(node.expr)
        if (exprType != null && exprType != BoolType) {
            printErrorTypeMismatch(node.expr.offset, BoolType, exprType, "here")
            return null
        }

        return BoolType
    }

    private fun resolveInt(node: IntNode): ResolvedType? {
        val value = try {
            node.value.toLong()
        } catch (e: NumberFormatException) {
            compilerMessagePrinter.printError(node.offset, "Invalid integer constant", "here")
            return null
        }

        node[IntConst.key] = IntConst(value)
        return IntType
    }

    private fun resolveBool(node: BoolNode): ResolvedType? {
        val value = when (node.value) {
            "true" -> true
            "false" -> false
            else -> {
                compilerMessagePrinter.printError(node.offset, "Unknown bool constant: '${node.value}'", "here")
                return null
            }
        }

        node[BoolConst.key] = BoolConst(value)
        return BoolType
    }

    private fun resolveName(node: NameNode): ResolvedType? {
        if (node.name == "$") {
            val symbol = node[ResolvedSymbol.key]
            check(symbol != null)
            return symbol.type
        }

        val symbol = symbolMap[node.name]
        if (symbol == null) {
            compilerMessagePrinter.printError(node.offset, "Unknown symbol: '${node.name}'", "here")
            return null
        }

        node[ResolvedSymbol.key] = symbol
        return symbol.type
    }

    private fun resolveExpr(node: ExprNode): ResolvedType? {
        return when (node) {
            is InvocationNode -> resolveInvocation(node)
            is ArithmeticNode -> resolveArithmetic(node)
            is CompareNode -> resolveCompare(node)
            is ArrowNode -> resolveArrow(node)
            is OrNode -> resolveOr(node)
            is AndNode -> resolveAnd(node)
            is NotNode -> resolveNot(node)
            is IntNode -> resolveInt(node)
            is BoolNode -> resolveBool(node)
            is NameNode -> resolveName(node)
        }
    }

    private fun resolveIf(node: IfNode): Boolean {
        resolveExpr(node.cond) ?: return false

        var trueContainer = logicContainer.clone().apply { addTrue(node.cond) }
        var falseContainer = logicContainer.clone().apply { addFalse(node.cond) }

        trueContainer = withLogicContainer(trueContainer) {
            if (!resolveBlock(node.trueBlock))
                return false
        }
        falseContainer = withLogicContainer(falseContainer) {
            node.falseBlock?.let {
                if (!resolveBlock(it))
                    return false
            }
        }
        logicContainer = LogicContainer.merge(trueContainer, falseContainer)
        return true
    }

    private fun resolveLet(node: LetNode): Boolean {
        symbolMap[node.name]?.let { existingSymbol ->
            compilerMessagePrinter.printRedeclarationError(node.nameOffset, node.name, existingSymbol)
            return false
        }

        if (node.type == null && node.initExpr == null) {
            compilerMessagePrinter.printError(node.nameOffset, "Uninitialized variable must have a declared type", "here")
            return false
        }

        val type = node.type?.let { resolveType(it) }
        val exprType = node.initExpr?.let {
            resolveExpr(it) ?: return false
        }
        if (type != null && exprType != null && type != exprType) {
            printErrorTypeMismatch(node.type.offset, type, exprType, "type is declared here")
            return false
        }

        val symbolType = type ?: exprType ?: TypeErrorMarker
        val declaredSymbol = ResolvedSymbol.LocalVariable(node.name, node, node.isMut, symbolType)
        symbolMap[node.name] = declaredSymbol

        if (node.initExpr != null) {
            logicContainer.addTrue(
                LogicCompare(
                LogicVar(declaredSymbol),
                LogicExpr.fromAst(node.initExpr) ?: return false,
                CompareNode.CompareOp.EQ)
            )
        }
        return true
    }

    private fun resolveAssign(node: AssignNode): Boolean {
        if (node.name !is NameNode) {
            compilerMessagePrinter.printError(node.offset, "Variable expected", "here")
            return false
        }

        resolveExpr(node.name) ?: return false
        resolveExpr(node.expr) ?: return false

        val symbol = node.name[ResolvedSymbol.key] ?: return false
        logicContainer.variableChanged(symbol)
        logicContainer.addTrue(
            LogicCompare(
            LogicExpr.fromAst(node.name) ?: return false,
            LogicExpr.fromAst(node.expr) ?: return false,
            CompareNode.CompareOp.EQ)
        )
        return true
    }

    private fun resolveReturn(node: ReturnNode): Boolean {
        resolveExpr(node.expr) ?: return false

        node.proofBlock?.let { proofBlock ->
            val replacedList = replaceContractOutputPattern(proofBlock, node.expr)
            if (!resolveProofBlock(ProofBlockNode(replacedList, proofBlock.offset)))
                return false
        }

        val function = currentFunction
        check(function != null)
        function.node.contract?.output?.let { block ->
            val replacedList = replaceContractOutputPattern(block, node.expr)
            compilerMessagePrinter.withContext(ErrorContext(node.offset)) {
                if (!resolveProofBlock(ProofBlockNode(replacedList, block.offset)))
                    return false
            }
        }

        logicContainer.addTrue(LogicBool(false))
        return true
    }

    private fun resolveLetEquals(node: LetEqualsNode): Boolean {
        symbolMap[node.name]?.let { existingSymbol ->
            compilerMessagePrinter.printRedeclarationError(node.nameOffset, node.name, existingSymbol)
            return false
        }

        val type = resolveExpr(node.expr) ?: return false

        symbolMap[node.name] = ResolvedSymbol.LetAlias(node.name, node, type)
        return true
    }

    private fun resolveProofFunction(node: ProofFunctionNode): Boolean {
        symbolMap[node.name]?.let { existingSymbol ->
            compilerMessagePrinter.printRedeclarationError(node.nameOffset, node.name, existingSymbol)
            return false
        }

        val arguments = node.arguments.map {
            resolveArgument(it) ?: return false
        }
        symbolMap[node.name] = ResolvedSymbol.ProofFunction(node.name, node, arguments)
        withLogicContainer(LogicContainer(compilerMessagePrinter)) {
            symbolMap.withScope {
                arguments.forEach {
                    symbolMap[it.name] = it
                }
                node.contract?.let { contract ->
                    resolveProofBlock(contract.input, skipVerification = true)
                    contract.output?.let { resolveProofBlock(it, onlyResolve = true) }
                }
                if (!resolveProofBlock(node.body))
                    // TODO print compiler error
                    return false
            }
        }
        return true
    }

    /**
     * Resolves and verifies a proof block [node].
     * @param skipVerification if `true`, assumes that all expressions are true and just adds them without verification
     * @param onlyResolve if `true`, doesn't verify or add expressions, just resolves them
     */
    private fun resolveProofBlock(node: ProofBlockNode, skipVerification: Boolean = false, onlyResolve: Boolean = false): Boolean {
        symbolMap.withScope {
            node.exprList.forEach {
                val result = when (it) {
                    is ExprNode -> resolveExpr(it) != null
                    is LetEqualsNode -> resolveLetEquals(it)
                    is ProofFunctionNode -> resolveProofFunction(it)
                    else -> error("Unknown proof element: ${it.javaClass}")
                }
                if (!result) return false
            }
        }

        if (onlyResolve) return true
        return logicContainer.verifyProofAndCollect(node.exprList, skipVerification = skipVerification)
    }

    private fun resolveCompilerCommand(node: CompilerCommandNode): Boolean {
        when (node.name) {
            // TODO add "axioms" -- prints all axioms (patterns and some description for others)
            "facts" -> logicContainer.printStatus(compilerMessagePrinter, node.offset)
            else -> {
                compilerMessagePrinter.printError(node.offset, "Unknown compiler command: '${node.name}'", "here")
                return false
            }
        }
        return true
    }

    private fun resolveBlock(node: BlockNode): Boolean {
        symbolMap.withScope {
            node.lines.forEach { statement ->
                when (statement) {
                    is BlockNode -> resolveBlock(statement)
                    is IfNode -> resolveIf(statement)
                    is LetNode -> resolveLet(statement)
                    is AssignNode -> resolveAssign(statement)
                    is ReturnNode -> resolveReturn(statement)
                    is ProofBlockNode -> resolveProofBlock(statement)
                    is CompilerCommandNode -> resolveCompilerCommand(statement)
                }.takeIf { it } ?: return false
            }
        }
        return true
    }

    private fun resolveArgument(node: ArgumentNode): ResolvedSymbol? {
        val type = resolveType(node.type) ?: return null
        val symbol = ResolvedSymbol.FunctionArgument(node.name, node, type)
        node[ResolvedSymbol.key] = symbol
        return symbol
    }

    private fun resolveFunctionDeclaration(node: FunctionNode): Boolean {
        val arguments = node.arguments.map {
            resolveArgument(it) ?: return false
        }
        val returnType = resolveType(node.returnType) ?: return false

        val symbol = ResolvedSymbol.Function(node.name, node, arguments, returnType)
        node[ResolvedSymbol.key] = symbol
        symbolMap[node.name] = symbol
        return true
    }

    private fun resolveFunctionBody(node: FunctionNode): Boolean {
        val symbol = node[ResolvedSymbol.key] as? ResolvedSymbol.Function
            ?: error("Unresolved function symbol: ${node.name}")

        withLogicContainer(logicContainer.clone()) {
            node.arguments.forEach { arg ->
                symbolMap[arg.name] = arg[ResolvedSymbol.key] ?: return false
            }

            node.contract?.input?.let { inputContract ->
                if (!resolveProofBlock(inputContract, skipVerification = true))
                    return false
            }

            try {
                check(currentFunction == null)
                currentFunction = symbol
                if (!resolveBlock(node.body))
                    return false
            } finally {
                currentFunction = null
            }
        }
        return true
    }

    fun resolveFile(topLevel: List<FunctionNode>): Boolean {
        // Create top-level file scope
        symbolMap.pushScope()

        topLevel.forEach {
            if (!resolveFunctionDeclaration(it))
                return false
        }

        // TODO exit if error occurred

        topLevel.forEach {
            if (!resolveFunctionBody(it))
                return false
        }
        return true
    }

    private fun assertType(found: ResolvedType?, expected: ResolvedType, offset: Int, hint: String = "here"): ResolvedType? {
        if (found != null && found != expected) {
            printErrorTypeMismatch(offset, expected, found, hint)
        }
        return found
    }

    private fun printErrorTypeMismatch(offset: Int, expected: ResolvedType, found: ResolvedType, hint: String) {
        compilerMessagePrinter.printError(offset, "Type mismatch: expected '$expected', found '$found'", hint)
    }

    private fun replaceContractOutputPattern(block: ProofBlockNode, dollarExpr: ExprNode?,
                                             additionalMap: Map<String, ExprNode> = emptyMap()): List<ProofElement> {
        val replaceBlock = block@ { expr: ExprNode ->
            if (expr is NameNode) {
                if (expr.name == "$") return@block dollarExpr
                additionalMap[expr.name]?.let { return@block it }
            }
            null
        }
        return block.exprList.map {
            when (it) {
                is ExprNode -> it.transform(replaceBlock)
                is LetEqualsNode -> LetEqualsNode(it.name, it.expr.transform(replaceBlock), it.nameOffset, it.offset)
                else -> error("Unknown proof element: ${it.javaClass}")
            }
        }
    }

    class ErrorContext(val offset: Int)

    class ScopeStack {
        private val symbolMap = mutableListOf<MutableMap<String, ResolvedSymbol>>()

        operator fun get(name: String): ResolvedSymbol? {
            symbolMap.asReversed().forEach { map ->
                map[name]?.let { return it }
            }
            return null
        }

        operator fun set(name: String, value: ResolvedSymbol) {
            symbolMap.last()[name] = value
        }

        fun pushScope() {
            symbolMap.add(mutableMapOf())
        }

        fun popScope() {
            symbolMap.removeLast()
        }

        inline fun <T> withScope(block: () -> T): T {
            try {
                pushScope()
                return block()
            } finally {
                popScope()
            }
        }
    }

    sealed class ResolvedSymbol(val name: String, val type: ResolvedType) {
        sealed class Callable(name: String, type: ResolvedType) : ResolvedSymbol(name, type) {
            abstract val arguments: List<ResolvedSymbol>
            abstract val contract: FunctionContract?
            abstract val returnType: ResolvedType
        }

        class Function(
            name: String,
            val node: FunctionNode,
            override val arguments: List<ResolvedSymbol>,
            override val returnType: ResolvedType
        ) : Callable(name, FunctionType(arguments, returnType)) {
            override val contract: FunctionContract?
                get() = node.contract

            override fun toString() = "function($name)"
        }

        class ProofFunction(
            name: String,
            val node: ProofFunctionNode,
            override val arguments: List<ResolvedSymbol>
        ) : Callable(name, TypeErrorMarker) {
            override val contract: FunctionContract?
                get() = node.contract

            override val returnType: ResolvedType
                get() = TypeErrorMarker
        }

        class FunctionArgument(name: String, val node: ArgumentNode, type: ResolvedType) : ResolvedSymbol(name, type) {
            // TODO return argument() later or in case of colliding names
            override fun toString() = "$name"
        }

        class LocalVariable(name: String, val node: LetNode, val isMut: Boolean, type: ResolvedType) : ResolvedSymbol(name, type) {
            //            override fun toString() = "local($name)"
            // TODO return local() later
            override fun toString() = "$name"
        }

        class LetAlias(name: String, val node: LetEqualsNode, type: ResolvedType) : ResolvedSymbol(name, type) {
            override fun toString() = "alias($name)"
        }

        class PatternName(name: String) : ResolvedSymbol(name, TypeErrorMarker) {
            override fun toString() = "\$$name"
        }

        companion object {
            val key = ContextKey<ResolvedSymbol>("resolved.symbol")
        }
    }

    class IntConst(val value: Long) {
        companion object {
            val key = ContextKey<IntConst>("int.const")
        }
    }

    class BoolConst(val value: Boolean) {
        companion object {
            val key = ContextKey<BoolConst>("bool.const")
        }
    }

    sealed class ResolvedType {
        companion object {
            val key = ContextKey<ResolvedType>("resolved.type")
        }
    }

    data object TypeErrorMarker : ResolvedType() {
        override fun toString() = "<error>"
    }

    data object IntType : ResolvedType() {
        override fun toString() = "int"
    }

    data object BoolType : ResolvedType() {
        override fun toString() = "bool"
    }

    class FunctionType(val arguments: List<ResolvedSymbol>, val returnType: ResolvedType) : ResolvedType() {
        override fun toString() = "function"
    }
}