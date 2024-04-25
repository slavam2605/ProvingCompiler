package org.example.verification

import org.example.*
import java.util.*

class LogicContainer(private val compilerMessagePrinter: CompilerMessagePrinter) {
    private val trueList = mutableListOf<LogicExpr>()
    private val compareEqualitySets = CompareEqualitySets()

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

    fun verifyProofAndCollect(list: List<ExprNode>) {
        val verifier = ProofVerifier(Collections.unmodifiableList(trueList), compareEqualitySets)
        val logicList = list.map { LogicExpr.fromAstNotNull(it) { return } }
        logicList.forEachIndexed { index, logicExpr ->
            if (!verifier.verifyExpr(logicExpr)) {
                compilerMessagePrinter.printError(list[index].offset, "Failed to prove the proof element", "here")
                return
            }

            // Don't split provided expressions, they may be needed later
            addTrue(logicExpr, noSplit = true)
        }
    }

    fun clone(): LogicContainer {
        return LogicContainer(compilerMessagePrinter).also {
            it.trueList.addAll(trueList)
            trueList.forEach { expr ->
                it.compareEqualitySets.addTrueExpr(expr)
            }
        }
    }

    override fun toString() = "$trueList"

    companion object {
        fun merge(left: LogicContainer, right: LogicContainer): LogicContainer {
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

            // Merge remaining expressions
            result.trueList.add(LogicOr(
                left.trueList.reduce { acc, next -> LogicAnd(acc, next) },
                right.trueList.reduce { acc, next -> LogicAnd(acc, next) }
            ))

            // Merge compare-equality sets
            result.compareEqualitySets.replaceWithMerge(left.compareEqualitySets, right.compareEqualitySets)

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