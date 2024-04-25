package org.example.verification

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
 *
 *  a; a -> b => b
 */
class ProofVerifier(
    private val trueList: List<LogicExpr>,
    private val compareEqualitySets: CompareEqualitySets
) {

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

    fun verifyExpr(expr: LogicExpr): Boolean {
        if (containsEqual(expr)) return true                // a -> a, considering all equality sets
        if (compareEqualitySets.isTrue(expr)) return true   // common comparison axioms

        return false
    }
}