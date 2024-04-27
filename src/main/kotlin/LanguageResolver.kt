package org.example

import org.example.AstNode.ContextKey
import org.example.verification.LogicCompare
import org.example.verification.LogicContainer
import org.example.verification.LogicExpr
import org.example.verification.LogicVar
import java.lang.NumberFormatException

class LanguageResolver(private val input: String) {
    private val symbolMap = ScopeStack()
    private val compilerMessagePrinter = CompilerMessagePrinter(input)
    private var logicContainer = LogicContainer(compilerMessagePrinter)

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

    private fun resolveIf(node: IfNode) {
        resolveExpr(node.cond)

        var trueContainer = logicContainer.clone().apply { addTrue(node.cond) }
        var falseContainer = logicContainer.clone().apply { addFalse(node.cond) }

        trueContainer = withLogicContainer(trueContainer) {
            resolveBlock(node.trueBlock)
        }
        falseContainer = withLogicContainer(falseContainer) {
            node.falseBlock?.let { resolveBlock(it) }
        }
        logicContainer = LogicContainer.merge(trueContainer, falseContainer)
    }

    private fun resolveLet(node: LetNode) {
        symbolMap[node.name]?.let { existingSymbol ->
            compilerMessagePrinter.printRedeclarationError(node.nameOffset, node.name, existingSymbol)
            return
        }

        if (node.type == null && node.initExpr == null) {
            compilerMessagePrinter.printError(node.nameOffset, "Uninitialized variable must have a declared type", "here")
        }

        val type = node.type?.let { resolveType(it) }
        val exprType = node.initExpr?.let { resolveExpr(it) }
        if (type != null && exprType != null && type != exprType) {
            printErrorTypeMismatch(node.type.offset, type, exprType, "type is declared here")
        }

        val symbolType = type ?: exprType ?: TypeErrorMarker
        val declaredSymbol = ResolvedSymbol.LocalVariable(node.name, node, node.isMut, symbolType)
        symbolMap[node.name] = declaredSymbol

        if (node.initExpr != null) {
            logicContainer.addTrue(
                LogicCompare(
                LogicVar(declaredSymbol),
                LogicExpr.fromAst(node.initExpr) ?: return,
                CompareNode.CompareOp.EQ)
            )
        }
    }

    private fun resolveAssign(node: AssignNode) {
        if (node.name !is NameNode) {
            compilerMessagePrinter.printError(node.offset, "Variable expected", "here")
            return
        }

        resolveExpr(node.name)
        resolveExpr(node.expr)

        val symbol = node.name[ResolvedSymbol.key] ?: return
        logicContainer.variableChanged(symbol)
        logicContainer.addTrue(
            LogicCompare(
            LogicExpr.fromAst(node.name) ?: return,
            LogicExpr.fromAst(node.expr) ?: return,
            CompareNode.CompareOp.EQ
        )
        )
    }

    private fun resolveReturn(node: ReturnNode) {
        resolveExpr(node.expr)
    }

    private fun resolveLetEquals(node: LetEqualsNode) {
        symbolMap[node.name]?.let { existingSymbol ->
            compilerMessagePrinter.printRedeclarationError(node.nameOffset, node.name, existingSymbol)
            return
        }

        val type = resolveExpr(node.expr) ?: return

        symbolMap[node.name] = ResolvedSymbol.LetAlias(node.name, node, type)
    }

    private fun resolveProofBlock(node: ProofBlockNode) {
        symbolMap.withScope {
            node.exprList.forEach {
                when (it) {
                    is ExprNode -> resolveExpr(it)
                    is LetEqualsNode -> resolveLetEquals(it)
                    else -> error("Unknown proof element: ${it.javaClass}")
                }
            }
        }

        logicContainer.verifyProofAndCollect(node.exprList)
    }

    private fun resolveCompilerCommand(node: CompilerCommandNode) {
        if (node.name != "facts") {
            compilerMessagePrinter.printError(node.offset, "Unknown compiler command: '${node.name}'", "here")
            return
        }

        logicContainer.printStatus(compilerMessagePrinter, node.offset)
    }

    fun resolveBlock(node: BlockNode) {
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
                }
            }
        }
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

    sealed class ResolvedSymbol(val type: ResolvedType) {
        class LocalVariable(val name: String, val node: LetNode, val isMut: Boolean, type: ResolvedType) : ResolvedSymbol(type) {
//            override fun toString() = "local($name)"
            // TODO return local() later
            override fun toString() = "$name"
        }

        class LetAlias(val name: String, val node: LetEqualsNode, type: ResolvedType) : ResolvedSymbol(type) {
            override fun toString() = "alias($name)"
        }

        class PatternName(val name: String) : ResolvedSymbol(TypeErrorMarker) {
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
}