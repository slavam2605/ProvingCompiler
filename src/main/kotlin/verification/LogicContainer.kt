package org.example.verification

import org.example.*
import java.util.*

class LogicContainer(private val compilerMessagePrinter: CompilerMessagePrinter) {
    internal val trueList = mutableListOf<LogicExpr>()
    internal val compareEqualitySets = CompareEqualitySets()

    fun addTrue(expr: LogicExpr, noSplit: Boolean = false) {
        trueList.add(expr)
        addToSet(expr, noSplit)
    }

    fun addFalse(expr: LogicExpr) { addTrue(LogicNot(expr)) }
    fun addTrue(node: ExprNode) = addTrue(LogicExpr.fromAstNotNull(node) { return })
    fun addFalse(node: ExprNode) = addFalse(LogicExpr.fromAstNotNull(node) { return })

    private fun addToSet(expr: LogicExpr, noSplit: Boolean) {
        if (noSplit) {
            compareEqualitySets.addTrueExpr(expr)
            return
        }

        splitTransformExpr(expr) { compareEqualitySets.addTrueExpr(it) }
    }

    fun variableChanged(symbol: LanguageResolver.ResolvedSymbol) {
        trueList.removeIf { expr ->
            expr.any { (it as? LogicVar)?.symbol === symbol }
        }
        compareEqualitySets.clear()
        trueList.forEach { addToSet(it, noSplit = false) }
    }

    /**
     * If [skipVerification] is true, then assume that all elements are true and just add them
     */
    fun verifyProofAndCollect(list: List<ProofElement>, skipVerification: Boolean) {
        val verifier = ProofVerifier(this)
        val letAliases = mutableMapOf<String, LogicExpr>()
        fun replaceAliases(expr: LogicExpr) = expr.replaceTree {
            ((expr as? LogicVar)?.symbol as? LanguageResolver.ResolvedSymbol.LetAlias)?.let { letAliases[it.name] }
        }

        val logicList = list.map { (it as? ExprNode)?.let { e -> LogicExpr.fromAst(e) } }
        logicList.forEachIndexed { index, proofElement ->
            when {
                proofElement != null -> {
                    val expr = replaceAliases(proofElement)
                    if (!skipVerification && !verifier.verifyExpr(expr)) {
                        compilerMessagePrinter.printError((list[index] as AstNode).offset, "Failed to prove the proof element", "here")
                        return
                    }

                    // Don't split provided expressions, they may be needed later
                    addTrue(expr, noSplit = true)
                }
                else -> {
                    val letEqualsNode = list[index] as LetEqualsNode
                    letAliases[letEqualsNode.name] = LogicExpr.fromAstNotNull(letEqualsNode.expr) { return }
                }
            }
        }
    }

    /**
     * Simplifies `expr` using simple rules like `false && a -> false`
     * and constant info from equality sets
     */
    internal fun simplifyExpr(originalExpr: LogicExpr) = originalExpr.recursiveTransform block@ { expr ->
        compareEqualitySets.getExprRange(expr).boolValue?.let {
            return@block LogicBool(it)
        }

        val leftBool = (expr.children.getOrNull(0) as? LogicBool)?.value
        val rightBool = (expr.children.getOrNull(1) as? LogicBool)?.value

        if (expr is LogicArrow) {
            when {
                leftBool == true -> return@block expr.right
                leftBool == false -> return@block LogicBool(true)
                rightBool == true -> return@block LogicBool(true)
                rightBool == false -> return@block LogicNot(expr.left)
            }
        }

        if (expr is LogicAnd) {
            when {
                leftBool == true -> return@block expr.right
                leftBool == false -> return@block LogicBool(false)
                rightBool == true -> return@block expr.left
                rightBool == false -> return@block LogicBool(false)
            }
        }

        if (expr is LogicOr) {
            when {
                leftBool == true -> return@block LogicBool(true)
                leftBool == false -> return@block expr.right
                rightBool == true -> return@block LogicBool(true)
                rightBool == false -> return@block expr.left
            }
        }

        if (expr is LogicNot) {
            leftBool?.let {
                return@block LogicBool(!it)
            }
            if (expr.expr is LogicNot)
                return@block expr.expr.expr
        }

        expr
    }

    fun clone(): LogicContainer {
        return LogicContainer(compilerMessagePrinter).also {
            it.trueList.addAll(trueList)
            trueList.forEach { expr ->
                it.compareEqualitySets.addTrueExpr(expr)
            }
        }
    }

    fun printStatus(printer: CompilerMessagePrinter, offset: Int) {
        printer.printInformation(offset, "Logic container dump")
        println("\tTrue facts:")
        trueList.forEach { println("\t\t$it") }
        compareEqualitySets.printStatus()
        println()
    }

    companion object {
        fun merge(left: LogicContainer, right: LogicContainer): LogicContainer {
            if (left.trueList.contains(LogicBool(false)))
                return right

            if (right.trueList.contains(LogicBool(false)))
                return left

            val result = LogicContainer(left.compilerMessagePrinter)

            // Filter out common expressions
            val leftIter = left.trueList.iterator()
            outer@ while (leftIter.hasNext()) {
                val leftExpr = leftIter.next()

                val rightIter = right.trueList.iterator()
                while (rightIter.hasNext()) {
                    val rightExpr = rightIter.next()

                    if (leftExpr == rightExpr) {
                        result.trueList.add(leftExpr)
                        leftIter.remove()
                        rightIter.remove()
                        continue@outer
                    }
                }
            }

            // Merge compare-equality sets
            result.compareEqualitySets.replaceWithMerge(left.compareEqualitySets, right.compareEqualitySets)

            // Merge remaining expressions
            val mergedTrueList = LogicOr(
                left.trueList.reduce { acc, next -> LogicAnd(acc, next) },
                right.trueList.reduce { acc, next -> LogicAnd(acc, next) }
            )
            splitTransformExpr(result.simplifyExpr(mergedTrueList)) { result.trueList.add(it) }

            return result
        }

        /**
         * Tries to simplify and split [expr] into multiple expressions combined with &&.
         * For each leaf expression [block] is called.
         * * `!(a < b) -> a >= b`
         * * `!(a < b || b < c) -> !(a < b) && !(b < c) -> a >= b && b >= c`
         */
        private fun splitTransformExpr(expr: LogicExpr, isNot: Boolean = false, block: (LogicExpr) -> Unit) {
            if (expr is LogicNot) {
                splitTransformExpr(expr.expr, !isNot, block)
                return
            }

            if (!isNot && expr is LogicAnd) {
                splitTransformExpr(expr.left, false, block)
                splitTransformExpr(expr.right, false, block)
                return
            }

            if (isNot && expr is LogicOr) {
                splitTransformExpr(expr.left, true, block)
                splitTransformExpr(expr.right, true, block)
                return
            }

            if (isNot) {
                if (expr is LogicCompare) {
                    block(LogicCompare(expr.left, expr.right, expr.op.negate()))
                    return
                }

                block(LogicNot(expr))
                return
            }

            block(expr)
        }
    }
}

sealed class LogicExpr(private val precedence: Int, vararg val children: LogicExpr) {
    abstract override fun equals(other: Any?): Boolean
    abstract override fun hashCode(): Int

    open fun shallowEquals(other: LogicExpr): Boolean {
        return this.javaClass == other.javaClass
    }

    fun any(predicate: (LogicExpr) -> Boolean): Boolean {
        return firstNotNull { if (predicate(it)) true else null } ?: false
    }

    private fun <T> firstNotNull(block: (LogicExpr) -> T?): T? {
        block(this)?.let { return it }
        children.forEach { child ->
            child.firstNotNull(block)?.let { return it }
        }
        return null
    }

    protected fun par(expr: LogicExpr): String {
        return if (expr.precedence < precedence)
            "($expr)" else "$expr"
    }

    companion object {
        fun fromAst(node: ExprNode): LogicExpr? {
            return when (node) {
                is InvocationNode -> {
                    val symbol = node.expr[LanguageResolver.ResolvedSymbol.key]
                            as? LanguageResolver.ResolvedSymbol.Function ?: return null
                    val arguments = node.arguments.map {
                        fromAst(it) ?: return null
                    }
                    LogicInvocation(symbol, arguments)
                }
                is ArithmeticNode -> {
                    val left = fromAst(node.left) ?: return null
                    val right = fromAst(node.right) ?: return null
                    LogicArithmetic(left, right, node.op)
                }
                is CompareNode -> {
                    val left = fromAst(node.left) ?: return null
                    val right = fromAst(node.right) ?: return null
                    LogicCompare(left, right, node.op)
                }
                is ArrowNode -> {
                    val left = fromAst(node.left) ?: return null
                    val right = fromAst(node.right) ?: return null
                    LogicArrow(left, right)
                }
                is OrNode -> {
                    val left = fromAst(node.left) ?: return null
                    val right = fromAst(node.right) ?: return null
                    LogicOr(left, right)
                }
                is AndNode -> {
                    val left = fromAst(node.left) ?: return null
                    val right = fromAst(node.right) ?: return null
                    LogicAnd(left, right)
                }
                is NotNode -> {
                    val expr = fromAst(node.expr) ?: return null
                    LogicNot(expr)
                }
                is IntNode -> {
                    val intValue = node[LanguageResolver.IntConst.key] ?: return null
                    LogicInt(intValue.value)
                }
                is BoolNode -> {
                    val boolValue = node[LanguageResolver.BoolConst.key] ?: return null
                    LogicBool(boolValue.value)
                }
                is NameNode -> {
                    val symbol = node[LanguageResolver.ResolvedSymbol.key] ?: return null
                    LogicVar(symbol)
                }
            }
        }

        inline fun fromAstNotNull(node: ExprNode, onNull: () -> Nothing): LogicExpr {
            return fromAst(node) ?: run {
                println("Warning: failed to add true expression $node")
                onNull()
            }
        }
    }
}

class LogicInvocation(
    val symbol: LanguageResolver.ResolvedSymbol.Function,
    val arguments: List<LogicExpr>
) : LogicExpr(1000, *arguments.toTypedArray()) {
    override fun shallowEquals(other: LogicExpr): Boolean {
        return other is LogicInvocation && symbol === other.symbol
    }

    override fun equals(other: Any?): Boolean {
        return other is LogicInvocation && symbol === other.symbol &&
                arguments.size == other.arguments.size &&
                arguments.zip(other.arguments).all { it.first == it.second }
    }

    override fun hashCode(): Int {
        return Objects.hash(symbol, *children)
    }

    override fun toString() = "${symbol.name}(${arguments.joinToString { it.toString() }})"
}

class LogicBool(val value: Boolean) : LogicExpr(1000) {
    override fun shallowEquals(other: LogicExpr) = this == other

    override fun equals(other: Any?): Boolean {
        return other is LogicBool && value == other.value
    }

    override fun hashCode(): Int {
        return Objects.hash(LogicBool::class.java, value)
    }

    override fun toString() = "$value"
}

class LogicInt(val value: Long) : LogicExpr(1000) {
    override fun shallowEquals(other: LogicExpr) = this == other

    override fun equals(other: Any?): Boolean {
        return other is LogicInt && value == other.value
    }

    override fun hashCode(): Int {
        return Objects.hash(value)
    }

    override fun toString() = "$value"
}

class LogicVar(val symbol: LanguageResolver.ResolvedSymbol) : LogicExpr(1000) {
    override fun shallowEquals(other: LogicExpr) = this == other

    override fun equals(other: Any?): Boolean {
        return other is LogicVar && symbol === other.symbol
    }

    override fun hashCode(): Int {
        return Objects.hash(symbol)
    }

    override fun toString() = "$symbol"
}

class LogicNot(val expr: LogicExpr) : LogicExpr(100, expr) {
    override fun equals(other: Any?): Boolean {
        return other is LogicNot && expr == other.expr
    }

    override fun hashCode(): Int {
        return Objects.hash(LogicNot::class.java, expr)
    }

    override fun toString() = "!${par(expr)}"
}

class LogicArrow(val left: LogicExpr, val right: LogicExpr) : LogicExpr(-10, left, right) {
    override fun equals(other: Any?): Boolean {
        return other is LogicArrow && left == other.left && right == other.right
    }

    override fun hashCode(): Int {
        return Objects.hash(LogicArrow::class.java, left, right)
    }

    override fun toString() = "${par(left)} -> ${par(right)}"
}

class LogicOr(val left: LogicExpr, val right: LogicExpr) : LogicExpr(0, left, right) {
    override fun equals(other: Any?): Boolean {
        return other is LogicOr && left == other.left && right == other.right
    }

    override fun hashCode(): Int {
        return Objects.hash(LogicOr::class.java, left, right)
    }

    override fun toString() = "${par(left)} || ${par(right)}"
}

class LogicAnd(val left: LogicExpr, val right: LogicExpr) : LogicExpr(10, left, right) {
    override fun equals(other: Any?): Boolean {
        return other is LogicAnd && left == other.left && right == other.right
    }

    override fun hashCode(): Int {
        return Objects.hash(LogicAnd::class.java, left, right)
    }

    override fun toString() = "${par(left)} && ${par(right)}"
}

class LogicCompare(val left: LogicExpr, val right: LogicExpr, val op: CompareNode.CompareOp) : LogicExpr(20, left, right) {
    override fun shallowEquals(other: LogicExpr): Boolean {
        return other is LogicCompare && op == other.op
    }

    override fun equals(other: Any?): Boolean {
        return other is LogicCompare && op == other.op && left == other.left && right == other.right
    }

    override fun hashCode(): Int {
        return Objects.hash(left, right, op)
    }

    override fun toString() = "${par(left)} $op ${par(right)}"
}

class LogicArithmetic(val left: LogicExpr, val right: LogicExpr, val op: ArithmeticNode.ArithmeticOp) : LogicExpr(30, left, right) {
    override fun shallowEquals(other: LogicExpr): Boolean {
        return other is LogicArithmetic && op == other.op
    }

    override fun equals(other: Any?): Boolean {
        return other is LogicArithmetic && op == other.op && left == other.left && right == other.right
    }

    override fun hashCode(): Int {
        return Objects.hash(left, right, op)
    }

    override fun toString() = "${par(left)} $op ${par(right)}"
}

/**
 * Recursively traverse tree and call [block] for each node.
 * If the result is not `null`, replace subtree with the result.
 */
fun LogicExpr.replaceTree(block: (LogicExpr) -> LogicExpr?): LogicExpr =
    transformTwoStep(blockBefore = block, blockAfter = { it })

/**
 * Recursively traverse tree and replace each node with a result of [block].
 */
fun LogicExpr.recursiveTransform(block: (LogicExpr) -> LogicExpr): LogicExpr =
    transformTwoStep(blockBefore = { null }, blockAfter = block)

private fun LogicExpr.transformTwoStep(blockBefore: (LogicExpr) -> LogicExpr?, blockAfter: (LogicExpr) -> LogicExpr): LogicExpr {
    blockBefore(this)?.let { return it }
    val recursiveResult = when (this) {
        is LogicInvocation -> LogicInvocation(symbol, arguments.map { it.transformTwoStep(blockBefore, blockAfter) })
        is LogicArrow -> LogicArrow(left.transformTwoStep(blockBefore, blockAfter), right.transformTwoStep(blockBefore, blockAfter))
        is LogicOr -> LogicOr(left.transformTwoStep(blockBefore, blockAfter), right.transformTwoStep(blockBefore, blockAfter))
        is LogicAnd -> LogicAnd(left.transformTwoStep(blockBefore, blockAfter), right.transformTwoStep(blockBefore, blockAfter))
        is LogicCompare -> LogicCompare(left.transformTwoStep(blockBefore, blockAfter), right.transformTwoStep(blockBefore, blockAfter), op)
        is LogicArithmetic -> LogicArithmetic(left.transformTwoStep(blockBefore, blockAfter), right.transformTwoStep(blockBefore, blockAfter), op)
        is LogicNot -> LogicNot(expr.transformTwoStep(blockBefore, blockAfter))
        is LogicVar, is LogicInt, is LogicBool -> this
    }
    return blockAfter(recursiveResult)
}