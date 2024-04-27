package org.example.verification

import org.example.CompareNode.CompareOp
import org.example.LanguageResolver.ResolvedSymbol

class ProofVerifier(
    private val trueList: List<LogicExpr>,
    private val compareEqualitySets: CompareEqualitySets
) {
    private val letAliases = mutableMapOf<String, LogicExpr>()

    fun addLetAlias(name: String, expr: LogicExpr) {
        letAliases[name] = expr
    }

    private fun areEqualWithEqualitySet(left: LogicExpr, right: LogicExpr): Boolean {
        if (compareEqualitySets.areEqual(left, right))
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

    private fun containsEqual(expr: LogicExpr): Boolean {
        return trueList.any { areEqualWithEqualitySet(it, expr) }
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
        for (axiom in axiomList) {
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

    private fun modusPonens(expr: LogicExpr): Boolean {
        return trueList.any { trueExpr ->
            if (trueExpr !is LogicArrow || !areEqualWithEqualitySet(trueExpr.right, expr))
                return@any false

            containsEqual(trueExpr.left)
        }
    }

    /**
     * Verify expression and return it with all aliases resolved
     */
    fun verifyExpr(exprWithAliases: LogicExpr): LogicExpr? {
        val expr = replaceAliases(exprWithAliases)
        if (containsEqual(expr)) return expr                // a -> a, considering all equality sets
        if (compareEqualitySets.isTrue(expr)) return expr   // verification with compare-equality sets
        if (matchesAxiom(expr)) return expr                 // check with axioms
        if (modusPonens(expr)) return expr                  // check with modus ponens

        return null
    }

    private fun replaceAliases(expr: LogicExpr): LogicExpr {
        return when (expr) {
            is LogicVar -> (expr.symbol as? ResolvedSymbol.LetAlias)?.let { letAliases[it.name] } ?: expr
            is LogicAnd -> LogicAnd(replaceAliases(expr.left), replaceAliases(expr.right))
            is LogicArithmetic -> LogicArithmetic(replaceAliases(expr.left), replaceAliases(expr.right), expr.op)
            is LogicArrow -> LogicArrow(replaceAliases(expr.left), replaceAliases(expr.right))
            is LogicCompare -> LogicCompare(replaceAliases(expr.left), replaceAliases(expr.right), expr.op)
            is LogicNot -> LogicNot(replaceAliases(expr.expr))
            is LogicOr -> LogicOr(replaceAliases(expr.left), replaceAliases(expr.right))
            is LogicBool -> expr
            is LogicInt -> expr
        }
    }

    companion object {
        private val a = LogicVar(ResolvedSymbol.PatternName("a"))
        private val b = LogicVar(ResolvedSymbol.PatternName("b"))
        private val c = LogicVar(ResolvedSymbol.PatternName("c"))

        private val axiomList: List<LogicExpr> = listOf(
            // !(a && b) -> !a || !b
            LogicArrow(LogicNot(LogicAnd(a, b)), LogicOr(LogicNot(a), LogicNot(b))),

            // a || b -> b || a
            LogicArrow(LogicOr(a, b), LogicOr(b, a)),

            // a || b -> !a -> b
            LogicArrow(LogicOr(a, b), LogicArrow(LogicNot(a), b)),

            // a -> !!a
            LogicArrow(a, LogicNot(LogicNot(a))),

            // (a -> b) -> (b -> c) -> a -> c
            LogicArrow(LogicArrow(a, b), LogicArrow(LogicArrow(b, c), LogicArrow(a, c))),

            // (a -> b) -> a -> a && b
            LogicArrow(LogicArrow(a, b), LogicArrow(a, LogicAnd(a, b))),

            // (a -> b) -> (a -> c) -> a -> b && c
            LogicArrow(LogicArrow(a, b), LogicArrow(LogicArrow(a, c), LogicArrow(a, LogicAnd(b, c)))),

            // (a -> false) -> !a
            LogicArrow(LogicArrow(a, LogicBool(false)), LogicNot(a))
        ) + createCompareAxioms()

        private fun createCompareAxioms(): List<LogicExpr> {
            val allCompareOps = CompareOp.entries
            val result = mutableListOf<LogicExpr>()

            // Negate: !(a <= b) -> a > b
            for (op in allCompareOps) {
                result.add(LogicArrow(LogicNot(LogicCompare(a, b, op)), LogicCompare(a, b, op.negate())))
            }

            // Weaken: a < b -> a <= b
            for (op in allCompareOps) {
                val weakOp = op.weaken() ?: continue
                result.add(LogicArrow(LogicCompare(a, b, op), LogicCompare(a, b, weakOp)))
            }

            // Flip: a > b -> b < a
            for (op in allCompareOps) {
                val flipOp = op.flip().takeIf { it != op } ?: continue
                result.add(LogicArrow(LogicCompare(a, b, op), LogicCompare(b, a, flipOp)))
            }

            // a < b && a > b -> false
            result.add(LogicArrow(LogicAnd(LogicCompare(a, b, CompareOp.LT), LogicCompare(a, b, CompareOp.GT)), LogicBool(false)))

            // a > b && a < b -> false
            result.add(LogicArrow(LogicAnd(LogicCompare(a, b, CompareOp.GT), LogicCompare(a, b, CompareOp.LT)), LogicBool(false)))

            // a <= b && a >= b -> a == b
            result.add(LogicArrow(LogicAnd(LogicCompare(a, b, CompareOp.LE), LogicCompare(a, b, CompareOp.GE)), LogicCompare(a, b, CompareOp.EQ)))

            // a >= b && a <= b -> a == b
            result.add(LogicArrow(LogicAnd(LogicCompare(a, b, CompareOp.GE), LogicCompare(a, b, CompareOp.LE)), LogicCompare(a, b, CompareOp.EQ)))

            return result
        }
    }
    /**
     *  a -> a
     *  a -> (b -> a)
     *  (a -> (b -> c)) -> ((a -> b) -> (a -> c))
     *  (!a -> !b) -> (b -> a)
     *  a; b -> a & b
     *  a & b -> a
     *  a & b -> b
     *  a -> a | b
     *  b -> a | b
     *  !!a -> a
     *  a | !a
     */
}