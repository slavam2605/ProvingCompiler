package org.example.verification

import org.example.CompareNode.CompareOp

class CompareEqualitySets {
    private val equalitySets = mutableListOf<ExprSetWithRange>()
    private val lessGraph = mutableMapOf<Int, MutableList<LessEdge>>()

    fun addTrueExpr(expr: LogicExpr) {
        // Add the expression with `true` as a const value
        val index = getOrCreateIndex(expr)
        equalitySets[index].range = ValueRange.exact(true)

        if (expr !is LogicCompare)
            return

        if (expr.left is LogicInt || expr.right is LogicInt) {
            return addConstIntExpr(expr)
        }

        if (expr.left is LogicBool || expr.right is LogicBool) {
            return addConstBoolExpr(expr)
        }

        val leftIndex = getOrCreateIndex(expr.left)
        val rightIndex = getOrCreateIndex(expr.right)
        when (expr.op) {
            CompareOp.EQ -> merge(leftIndex, rightIndex)
            CompareOp.LT -> addLessEdge(leftIndex, rightIndex, true)
            CompareOp.LE -> addLessEdge(leftIndex, rightIndex, false)
            CompareOp.GT -> addLessEdge(rightIndex, leftIndex, true)
            CompareOp.GE -> addLessEdge(rightIndex, leftIndex, false)
            CompareOp.NEQ -> { /* No useful information */ }
        }
    }

    fun clear() {
        equalitySets.clear()
        lessGraph.clear()
    }

    fun isTrue(expr: LogicExpr): Boolean {
        if (expr !is LogicCompare)
            return false

        if (expr.op == CompareOp.EQ) return areEqual(expr.left, expr.right)
        if (expr.op == CompareOp.NEQ) return areNotEqual(expr.left, expr.right)
        if (expr.op == CompareOp.LT) return areLess(expr.left, expr.right, true)
        if (expr.op == CompareOp.LE) return areLess(expr.left, expr.right, false)
        if (expr.op == CompareOp.GT) return areLess(expr.right, expr.left, true)
        if (expr.op == CompareOp.GE) return areLess(expr.right, expr.left, false)

        return false
    }

    private fun areLess(left: LogicExpr, right: LogicExpr, isStrict: Boolean): Boolean {
        if (left is LogicInt || right is LogicInt)
            return areLessConst(left, right, isStrict)

        val leftIndex = tryGetIndex(left) ?: return false
        val rightIndex = tryGetIndex(right) ?: return false

        // If we want to check that a <= b, and a == b, return true
        if (!isStrict && leftIndex == rightIndex) return true

        // Try to compare int ranges for a and b
        if (equalitySets[leftIndex].range.forAllLess(equalitySets[rightIndex].range, isStrict))
            return true

        // Check with dfs for transitive less
        return dfsIsReachable(leftIndex, rightIndex, isStrict, mutableSetOf())
    }

    private fun areLessConst(left: LogicExpr, right: LogicExpr, isStrict: Boolean): Boolean {
        if (left is LogicInt && right is LogicInt)
            return if (isStrict) left.value < right.value else left.value <= right.value

        if (right is LogicInt) {
            val value = right.value
            val index = tryGetIndex(left) ?: return false
            return equalitySets[index].range.forAllLess(ValueRange.exact(value), isStrict)
        }

        val value = (left as LogicInt).value
        val index = tryGetIndex(right) ?: return false
        return equalitySets[index].range.forAllGreater(ValueRange.exact(value), isStrict)
    }

    private fun areNotEqual(left: LogicExpr, right: LogicExpr): Boolean {
        val leftRange = tryGetIndex(left)?.let { equalitySets[it].range }
            ?: (left as? LogicInt)?.let { ValueRange.exact(it.value) }
            ?: return false

        val rightIndex = tryGetIndex(right)?.let { equalitySets[it].range }
            ?: (right as? LogicInt)?.let { ValueRange.exact(it.value) }
            ?: return false

        return leftRange.isDisjointWith(rightIndex)
    }

    fun areEqual(left: LogicExpr, right: LogicExpr): Boolean {
        val leftIndex = tryGetIndex(left) ?: return false
        val rightIndex = tryGetIndex(right) ?: return false
        return leftIndex == rightIndex
    }

    fun getExprRange(expr: LogicExpr): ValueRange {
        val index = tryGetIndex(expr) ?: return ValueRange.NullRange
        return equalitySets[index].range
    }

    fun replaceWithMerge(left: CompareEqualitySets, right: CompareEqualitySets) {
        // Clear all info before merging
        clear()

        // Add all expressions from both sets
        left.equalitySets.forEach { set ->
            set.set.forEach { expr -> getOrCreateIndex(expr) }
        }
        right.equalitySets.forEach { set ->
            set.set.forEach { expr -> getOrCreateIndex(expr) }
        }

        // Merge all elements that are equal in both sets
        for (i in equalitySets.indices) {
            val iExpr = equalitySets[i].set.firstOrNull() ?: continue
            for (j in i + 1 until equalitySets.size) {
                val jExpr = equalitySets[j].set.firstOrNull() ?: continue
                if (left.areEqual(iExpr, jExpr) && right.areEqual(iExpr, jExpr)) {
                    merge(i, j)
                }
            }
        }

        // Merge value ranges
        for (i in equalitySets.indices) {
            val expr = equalitySets[i].set.firstOrNull() ?: continue
            equalitySets[i].range = left.getExprRange(expr).union(right.getExprRange(expr))
        }

        // Merge less graphs
        for (i in equalitySets.indices) {
            val iExpr = equalitySets[i].set.firstOrNull() ?: continue
            for (j in i + 1 until equalitySets.size) {
                val jExpr = equalitySets[j].set.firstOrNull() ?: continue

                // Check that iExpr <= jExpr for both graphs
                if (left.areLess(iExpr, jExpr, false) && right.areLess(iExpr, jExpr, false)) {
                    // Add edge anyway, but isStrict only if they are reachable in both graphs with isStrict=true
                    lessGraph.getOrPut(i) { mutableListOf() }.add(
                        LessEdge(j, left.areLess(iExpr, jExpr, true) && right.areLess(iExpr, jExpr, true))
                    )
                }

                // The same check, but in reversed order (because i < j, so we have to check both directions)
                if (left.areLess(jExpr, iExpr, false) && right.areLess(jExpr, iExpr, false)) {
                    lessGraph.getOrPut(j) { mutableListOf() }.add(
                        LessEdge(i, left.areLess(jExpr, iExpr, true) && right.areLess(jExpr, iExpr, true))
                    )
                }
            }
        }
    }

    private fun dfsIsReachable(from: Int, to: Int, isStrictNeeded: Boolean, visited: MutableSet<Int>): Boolean {
        if (from == to) {
            // isStrictNeeded must be false at this point
            // Either it was not needed from the beginning, or we already met a '<' on the way here
            return !isStrictNeeded
        }

        if (from in visited)
            return false

        visited.add(from)
        lessGraph[from]?.forEach { edge ->
            // '<' is still needed if "it was needed" and "this edge is not strict"
            val isStrictStillNeeded = isStrictNeeded && !edge.isStrict
            if (dfsIsReachable(edge.toIndex, to, isStrictStillNeeded, visited))
                return true
        }

        return false
    }

    private fun addConstBoolExpr(compareExpr: LogicCompare) {
        val (expr, boolValue) = if (compareExpr.right is LogicBool)
            compareExpr.left to compareExpr.right.value
        else
            compareExpr.right to (compareExpr.left as LogicBool).value

        val index = getOrCreateIndex(expr)
        when (compareExpr.op) {
            CompareOp.EQ -> equalitySets[index].range = ValueRange.exact(boolValue)
            CompareOp.NEQ -> equalitySets[index].range = ValueRange.exact(!boolValue)
            else -> error("Bool values can only be compared with == and !=")
        }
    }

    private fun addConstIntExpr(compareExpr: LogicCompare) {
        if (compareExpr.left is LogicInt && compareExpr.right is LogicInt)
            return

        val (expr, intValue, op) = if (compareExpr.right is LogicInt)
            Triple(compareExpr.left, compareExpr.right.value, compareExpr.op)
        else
            Triple(compareExpr.right, (compareExpr.left as LogicInt).value, compareExpr.op.flip())

        val index = getOrCreateIndex(expr)
        when (op) {
            CompareOp.EQ -> equalitySets[index].range = ValueRange.exact(intValue)
            CompareOp.LE -> equalitySets[index].range = equalitySets[index].range.intersect(ValueRange.longRange(null, intValue))
            CompareOp.LT -> equalitySets[index].range = equalitySets[index].range.intersect(ValueRange.longRange(null, intValue - 1))
            CompareOp.GE -> equalitySets[index].range = equalitySets[index].range.intersect(ValueRange.longRange(intValue, null))
            CompareOp.GT -> equalitySets[index].range = equalitySets[index].range.intersect(ValueRange.longRange(intValue + 1, null))
            else -> {}
        }
    }

    private fun addLessEdge(fromIndex: Int, toIndex: Int, isStrict: Boolean) {
        // Try to update an existing edge
        lessGraph[fromIndex]?.forEach { edge ->
            if (edge.toIndex == toIndex) {
                // Update isStrict: '<' doesn't change, '<=' can turn into '<'
                edge.isStrict = edge.isStrict || isStrict
                return
            }
        }

        // Add a new edge
        lessGraph.getOrPut(fromIndex) { mutableListOf() }
            .add(LessEdge(toIndex, isStrict))
    }

    private fun merge(leftIndex: Int, rightIndex: Int) {
        // Merge two equality sets
        equalitySets[leftIndex].mergeWith(equalitySets[rightIndex])
        equalitySets[rightIndex].clear()

        // Merge two compare sets (right < x => left < x), remove edges 'left < right' and 'right < left'
        val leftLess = lessGraph.getOrPut(leftIndex) { mutableListOf() }
        val rightLess = lessGraph.getOrPut(rightIndex) { mutableListOf() }
        leftLess.addAll(rightLess)
        leftLess.removeIf { it.toIndex == leftIndex || it.toIndex == rightIndex }

        // Replace all occurrences of "right" with "left" in compare graph
        lessGraph.remove(rightIndex)
        lessGraph.forEach { (_, list) ->
            for (index in list.indices) {
                if (list[index].toIndex == rightIndex) {
                    list[index].toIndex = leftIndex
                }
            }
        }
    }

    private fun getOrCreateIndex(expr: LogicExpr): Int {
        // Try to find an existing index
        tryGetIndex(expr)?.let { return it }

        // Try to find an empty set to use
        equalitySets.forEachIndexed { i, set ->
            if (set.set.isEmpty()) {
                set.set.add(expr)
                return i
            }
        }

        // Allocate a new set
        equalitySets.add(ExprSetWithRange(hashSetOf(expr)))
        return equalitySets.lastIndex
    }

    private fun tryGetIndex(expr: LogicExpr): Int? {
        return equalitySets.indexOfFirst { it.set.contains(expr) }.takeIf { it >= 0 }
    }

    fun printStatus() {
        val nonTrivialSets = equalitySets.filter {
            it.set.size > 1 || it.set.size == 1 && it.range != ValueRange.NullRange
        }
        if (nonTrivialSets.isNotEmpty()) {
            println("\tEquality sets:")
            for (set in nonTrivialSets) {
                println("\t\t$set")
            }
        }
        if (lessGraph.any { (_, list) -> list.isNotEmpty() }) {
            println("\tLess graph:")
            lessGraph.forEach { (from, list) ->
                list.forEach { edge ->
                    println("\t\t${equalitySets[from]} ${if (edge.isStrict) "<" else "<="} ${equalitySets[edge.toIndex]}")
                }
            }
        }
    }

    data class LessEdge(var toIndex: Int, var isStrict: Boolean)

    class ExprSetWithRange(val set: HashSet<LogicExpr>, var range: ValueRange = ValueRange.NullRange) {
        fun mergeWith(other: ExprSetWithRange) {
            set.addAll(other.set)
            range = range.intersect(other.range)
        }

        fun clear() {
            set.clear()
            range = ValueRange.NullRange
        }

        override fun toString(): String {
            val range = if (range == ValueRange.NullRange) "" else " | $range"
            return "[${set.joinToString()}$range]"
        }
    }

    data class ValueRange(val from: Long?, val to: Long?, val boolValue: Boolean?) {
        fun intersect(other: ValueRange): ValueRange {
            return ValueRange(
                listOfNotNull(from, other.from).maxOrNull(),
                listOfNotNull(to, other.to).minOrNull(),
                boolValue.takeIf { boolValue == other.boolValue }
            )
        }

        fun union(other: ValueRange): ValueRange {
            return ValueRange(
                from?.let { sf -> other.from?.let { of -> minOf(sf, of) } },
                to?.let { st -> other.to?.let { ot -> maxOf(st, ot) } },
                boolValue.takeIf { boolValue == other.boolValue }
            )
        }

        fun forAllLess(other: ValueRange, isStrict: Boolean): Boolean {
            check(boolValue == null)
            val selfTo = to ?: Long.MAX_VALUE
            val otherFrom = other.from ?: Long.MIN_VALUE
            return if (isStrict) {
                selfTo < otherFrom
            } else {
                selfTo <= otherFrom
            }
        }

        fun forAllGreater(other: ValueRange, isStrict: Boolean): Boolean {
            check(boolValue == null)
            val selfFrom: Long = from ?: Long.MIN_VALUE
            val otherTo: Long = other.to ?: Long.MAX_VALUE
            return if (isStrict) {
                selfFrom > otherTo
            } else {
                selfFrom >= otherTo
            }
        }

        fun isDisjointWith(other: ValueRange): Boolean {
            check(boolValue == null)
            return forAllLess(other, true) || forAllGreater(other, true)
        }

        override fun toString() = when {
            boolValue != null -> boolValue.toString()
            from == null && to == null -> "<empty>"
            from == to -> "$from"
            from != null && to != null -> "$from..$to"
            from != null -> ">= $from"
            else -> "<= $to"
        }

        companion object {
            val NullRange = ValueRange(null, null, null)

            fun exact(value: Long) = ValueRange(value, value, null)
            fun exact(value: Boolean) = ValueRange(null, null, value)

            fun longRange(from: Long?, to: Long?) = ValueRange(from, to, null)
        }
    }
}