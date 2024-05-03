package org.example.verification

import org.example.*
import org.example.CompareNode.CompareOp
import org.example.LanguageResolver.ResolvedSymbol

class ProofVerifier(
    private val parent: ProofVerifier?,
    private val context: List<LogicExpr>,
    private val logicContainer: LogicContainer
) {
    private val localTrueList = mutableListOf<LogicExpr>()
    private val letAliases = mutableMapOf<String, LogicExpr>()

    private val trueSequence: Sequence<LogicExpr>
        get() = (parent?.trueSequence ?: logicContainer.trueList.asSequence()) + localTrueList.asSequence()

    init {
        localTrueList.addAll(context)
    }

    private fun tryGetAlias(expr: LogicExpr): LogicExpr? {
        val letAlias = (expr as? LogicVar)?.symbol as? ResolvedSymbol.LetAlias ?: return null
        return letAliases[letAlias.name] ?: parent?.tryGetAlias(expr)
    }

    private fun addTrueExpr(expr: LogicExpr) {
        localTrueList.add(expr)
        val exprWithContext = context.foldRight(expr) { contextExpr, acc -> LogicArrow(contextExpr, acc) }
        if (parent != null) {
            parent.addTrueExpr(exprWithContext)
        } else {
            logicContainer.addTrue(expr, noSplit = true)
        }
    }

    /**
     * Given [invocationExpr] `foo(expr1, expr2, ...)` where `foo` is `fun(a, b, ...)`
     * replaces `a` with `expr1`, `b` with `expr2` etc. in [expr]
     */
    private fun replaceWithInvocationArguments(expr: LogicExpr, invocationExpr: LogicInvocation) =
        expr.replaceTree { innerExpr ->
            val symbol = (innerExpr as? LogicVar)?.symbol ?: return@replaceTree null
            val index = invocationExpr.symbol.arguments.indexOfFirst { it === symbol }.takeIf { it >= 0 }
                ?: return@replaceTree null
            invocationExpr.arguments[index]
        }

    private fun applyOutputContract(invocationExpr: LogicInvocation) {
        val output = invocationExpr.symbol.contract?.output ?: return
        val exprList = output.exprList
            .map { LogicExpr.fromAstNotNull(it as ExprNode) { return } }
            .map { replaceWithInvocationArguments(it, invocationExpr) }
        exprList.forEach {
            addTrueExpr(it)
        }
    }

    private fun checkInputContract(invocationExpr: LogicInvocation): Boolean {
        val input = invocationExpr.symbol.contract?.input ?: return true
        // TODO print compiler error if exprList contains something other than ExprNode
        val exprList = input.exprList
            .map { LogicExpr.fromAstNotNull(it as ExprNode) { return false } }
            .map { replaceWithInvocationArguments(it, invocationExpr) }
        exprList.forEachIndexed { index, inputExpr ->
            if (!verifyExpr(inputExpr)) {
                val node = (invocationExpr.symbol as ResolvedSymbol.ProofFunction).node
                val exprNode = input.exprList[index] as ExprNode
                logicContainer.compilerMessagePrinter.printError(exprNode.offset, "Failed to prove input contract", "for proof '${node.name}'")
                return false
            }
        }
        return true
    }

    /**
     * If [skipVerification] is true, then assume that all elements are true and just add them.
     * @return `true` if verification was successful. Always `true` if [skipVerification] is `true`.
     */
    fun verifyProofAndCollect(list: List<ProofElement>, skipVerification: Boolean): Boolean {
        list.forEach { node ->
            when (node) {
                is ExprNode -> {
                    val expr = LogicExpr.fromAstNotNull(node) { return false }
                        .replaceTree { tryGetAlias(it) }

                    if (expr is LogicInvocation && expr.symbol is ResolvedSymbol.ProofFunction)  {
                        if (skipVerification) {
                            error("Can't skip verification for proof invocation")
                        }
                        logicContainer.compilerMessagePrinter.withContext(LanguageResolver.ErrorContext(node.offset)) {
                            if (!checkInputContract(expr))
                                return false
                        }
                        applyOutputContract(expr)
                        return@forEach
                    }

                    if (!skipVerification && !verifyExpr(expr)) {
                        // TODO add expansion of let-elements
                        logicContainer.compilerMessagePrinter.printError(node.offset, "Failed to prove the proof element", "here")
                        return false
                    }

                    addTrueExpr(expr)
                }
                is LetEqualsNode -> {
                    letAliases[node.name] = LogicExpr.fromAstNotNull(node.expr) { return false }
                }
                is ProofFunctionNode -> { /* Skip proof declaration */ }
                is DeductionBlockNode -> {
                    check(!skipVerification) { "`skipVerification == false` is not allowed for deduction blocks" }
                    val context = node.inputs.map {
                        LogicExpr.fromAstNotNull(it) { return false }
                    }
                    ProofVerifier(this, context, logicContainer)
                        .verifyProofAndCollect(node.body.exprList, false)
                }
                else -> error("Unknown proof element: ${node.javaClass}")
            }
        }
        return true
    }

    private fun areEqualWithEqualitySet(left: LogicExpr, right: LogicExpr): Boolean {
        if (logicContainer.compareEqualitySets.areEqual(left, right))
            return true

        if (!left.shallowEquals(right))
            return false

        if (left.children.size != right.children.size)
            return false

        for (i in left.children.indices) {
            if (!areEqualWithEqualitySet(left.children[i], right.children[i]))
                return false
        }

        return true
    }

    private fun equalsTrue(expr: LogicExpr): Boolean {
        val simplifiedExpr = logicContainer.simplifyExpr(expr)
        return simplifiedExpr is LogicBool && simplifiedExpr.value
    }

    private fun containsEqual(expr: LogicExpr): Boolean {
        return trueSequence.any { areEqualWithEqualitySet(it, expr) }
    }

    /**
     * Matches expressions like `a >= b && b > c -> a > c` and checks that it is true (for all ops and orders)
     */
    private fun matchesComplexCompareAxiom(expr: LogicExpr): Boolean {
        if (expr !is LogicArrow) return false
        if (expr.left !is LogicAnd) return false
        val first = expr.left.left as? LogicCompare ?: return false
        val second = expr.left.right as? LogicCompare ?: return false
        val third = expr.right as? LogicCompare ?: return false

        val sets = CompareEqualitySets()
        sets.addTrueExpr(first)
        sets.addTrueExpr(second)
        return sets.isTrue(third)
    }

    private fun matchesAxiom(expr: LogicExpr): Boolean {
        for (axiom in axiomList + logicContainer.axiomList) {
            if (matchesAxiom(expr, axiom, mutableMapOf()))
                return true
        }
        return matchesComplexCompareAxiom(expr)
    }

    private fun matchesAxiom(expr: LogicExpr, axiom: LogicExpr, patternMap: MutableMap<String, LogicExpr>): Boolean {
        if (axiom is LogicVar && axiom.symbol is ResolvedSymbol.PatternName) {
            val name = axiom.symbol.name
            val patternExpr = patternMap[name] ?: run {
                patternMap[name] = expr
                return true
            }
            return areEqualWithEqualitySet(expr, patternExpr)
        }

        if (!expr.shallowEquals(axiom))
            return false

        if (expr.children.size != axiom.children.size)
            return false

        for (i in expr.children.indices) {
            if (!matchesAxiom(expr.children[i], axiom.children[i], patternMap))
                return false
        }

        return true
    }

    /**
     * Tries to find true expression `a -> b -> ... -> z -> expr`, where all `a`, `b`, ..., `z` are true
     */
    private fun modusPonens(expr: LogicExpr): Boolean {
        fun splitArrowChain(expr: LogicArrow, target: LogicExpr): List<LogicExpr>? {
            val list = mutableListOf<LogicExpr>()
            var currentArrow = expr
            while (true) {
                list.add(currentArrow.left)
                if (areEqualWithEqualitySet(currentArrow.right, target)) {
                    return list
                }
                if (currentArrow.right is LogicArrow) {
                    currentArrow = currentArrow.right as LogicArrow
                    continue
                }
                return null
            }
        }

        return trueSequence.any { trueExpr ->
            if (trueExpr !is LogicArrow)
                return@any false

            val chain = splitArrowChain(trueExpr, expr) ?: return@any false
            chain.all { containsEqual(it) }
        }
    }

    fun verifyExpr(expr: LogicExpr): Boolean {
        if (equalsTrue(expr)) return true                   // a == true
        if (containsEqual(expr)) return true                // a -> a, considering all equality sets
        if (logicContainer.compareEqualitySets.isTrue(expr))
            return true                                     // verification with compare-equality sets
        if (matchesAxiom(expr)) return true                 // check with axioms
        if (modusPonens(expr)) return true                  // check with modus ponens

        return false
    }

    companion object {
        private val a = LogicVar(ResolvedSymbol.PatternName("a", LanguageResolver.BoolType))
        private val b = LogicVar(ResolvedSymbol.PatternName("b", LanguageResolver.BoolType))
        private val c = LogicVar(ResolvedSymbol.PatternName("c", LanguageResolver.BoolType))
        private val x = LogicVar(ResolvedSymbol.PatternName("x", LanguageResolver.IntType))
        private val y = LogicVar(ResolvedSymbol.PatternName("y", LanguageResolver.IntType))

        private val axiomList: List<LogicExpr> = listOf(
            // a -> b -> a
            LogicArrow(a, LogicArrow(b, a)),

            // (a -> b) -> (a -> b -> c) -> a -> c
            LogicArrow(LogicArrow(a, b), LogicArrow(LogicArrow(a, LogicArrow(b, c)), LogicArrow(a, c))),

            // a -> b -> a && b
            LogicArrow(a, LogicArrow(b, LogicAnd(a, b))),

            // a && b -> a
            LogicArrow(LogicAnd(a, b), a),

            // a && b -> b
            LogicArrow(LogicAnd(a, b), b),

            // a -> a || b
            LogicArrow(a, LogicOr(a, b)),

            // b -> a || b
            LogicArrow(b, LogicOr(a, b)),

            // (a -> c) -> (b -> c) -> a || b -> c
            LogicArrow(LogicArrow(a, c), LogicArrow(LogicArrow(b, c), LogicArrow(LogicOr(a, b), c))),

            // (a -> b) -> (a -> !b) -> !a
            LogicArrow(LogicArrow(a, b), LogicArrow(LogicArrow(a, LogicNot(b)), LogicNot(a))),

            // !!a -> a
            LogicArrow(LogicNot(LogicNot(a)), a)
        ) + createCompareAxioms()

        private fun createCompareAxioms(): List<LogicExpr> {
            val allCompareOps = CompareOp.entries
            val result = mutableListOf<LogicExpr>()

            // Negate: !(x <= y) -> x > y
            for (op in allCompareOps) {
                result.add(LogicArrow(LogicNot(LogicCompare(x, y, op)), LogicCompare(x, y, op.negate())))
            }

            // Weaken: x < y -> x <= y
            for (op in allCompareOps) {
                val weakOp = op.weaken() ?: continue
                result.add(LogicArrow(LogicCompare(x, y, op), LogicCompare(x, y, weakOp)))
            }

            // Flip: x > y -> y < x
            for (op in allCompareOps) {
                val flipOp = op.flip().takeIf { it != op } ?: continue
                result.add(LogicArrow(LogicCompare(x, y, op), LogicCompare(y, x, flipOp)))
            }

            // Enforce: !(x == y) -> x <= y -> x < y
            for (op in allCompareOps) {
                val weakOp = op.weaken() ?: continue
                result.add(LogicArrow(LogicNot(LogicCompare(x, y, CompareOp.EQ)), LogicArrow(
                    LogicCompare(x, y, weakOp), LogicCompare(x, y, op)
                )))
            }

            // x < y && x > y -> false
            result.add(LogicArrow(LogicAnd(LogicCompare(x, y, CompareOp.LT), LogicCompare(x, y, CompareOp.GT)), LogicBool(false)))

            // x > y && x < y -> false
            result.add(LogicArrow(LogicAnd(LogicCompare(x, y, CompareOp.GT), LogicCompare(x, y, CompareOp.LT)), LogicBool(false)))

            // x < y && y < x -> false
            result.add(LogicArrow(LogicAnd(LogicCompare(x, y, CompareOp.LT), LogicCompare(y, x, CompareOp.LT)), LogicBool(false)))

            // x > y && y > x -> false
            result.add(LogicArrow(LogicAnd(LogicCompare(x, y, CompareOp.GT), LogicCompare(y, x, CompareOp.GT)), LogicBool(false)))

            // x <= y && x >= y -> x == y
            result.add(LogicArrow(LogicAnd(LogicCompare(x, y, CompareOp.LE), LogicCompare(x, y, CompareOp.GE)), LogicCompare(x, y, CompareOp.EQ)))

            // x >= y && x <= y -> x == y
            result.add(LogicArrow(LogicAnd(LogicCompare(x, y, CompareOp.GE), LogicCompare(x, y, CompareOp.LE)), LogicCompare(x, y, CompareOp.EQ)))

            return result
        }
    }
}