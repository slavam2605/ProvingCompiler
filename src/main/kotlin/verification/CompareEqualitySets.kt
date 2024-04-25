package org.example.verification

import org.example.CompareNode

class CompareEqualitySets {
    private val equalitySets = mutableListOf<HashSet<LogicExpr>>()
    private val lessGraph = mutableMapOf<Int, MutableList<LessEdge>>()

    fun addTrueExpr(expr: LogicExpr) {
        if (expr !is LogicCompare)
            return

        val leftIndex = getOrCreateIndex(expr.left)
        val rightIndex = getOrCreateIndex(expr.right)
        when (expr.op) {
            CompareNode.CompareOp.EQ -> merge(leftIndex, rightIndex)
            CompareNode.CompareOp.LT -> addLessEdge(leftIndex, rightIndex, true)
            CompareNode.CompareOp.LE -> addLessEdge(leftIndex, rightIndex, false)
            CompareNode.CompareOp.GT -> addLessEdge(rightIndex, leftIndex, true)
            CompareNode.CompareOp.GE -> addLessEdge(rightIndex, leftIndex, false)
            CompareNode.CompareOp.NEQ -> { /* No useful information */ }
        }
    }

    fun clear() {
        equalitySets.clear()
        lessGraph.clear()
    }

    fun isTrue(expr: LogicExpr): Boolean {
        if (expr !is LogicCompare)
            return false

        if (expr.op == CompareNode.CompareOp.EQ) return areEqual(expr.left, expr.right)
        if (expr.op == CompareNode.CompareOp.LT) return areLess(expr.left, expr.right, true)
        if (expr.op == CompareNode.CompareOp.LE) return areLess(expr.left, expr.right, false)
        if (expr.op == CompareNode.CompareOp.GT) return areLess(expr.right, expr.left, true)
        if (expr.op == CompareNode.CompareOp.GE) return areLess(expr.right, expr.left, false)

        return false
    }

    private fun areLess(left: LogicExpr, right: LogicExpr, isStrict: Boolean): Boolean {
        val leftIndex = tryGetIndex(left) ?: return false
        val rightIndex = tryGetIndex(right) ?: return false

        // If we want to check that a <= b, and a == b, return true
        if (!isStrict && leftIndex == rightIndex) return true

        // Check with dfs for transitive less
        return dfsIsReachable(leftIndex, rightIndex, isStrict, mutableSetOf())
    }

    fun areEqual(left: LogicExpr, right: LogicExpr): Boolean {
        val leftIndex = tryGetIndex(left) ?: return false
        val rightIndex = tryGetIndex(right) ?: return false
        return leftIndex == rightIndex
    }

    fun replaceWithMerge(left: CompareEqualitySets, right: CompareEqualitySets) {
        // Clear all info before merging
        clear()

        // Add all expressions from both sets
        left.equalitySets.forEach { set ->
            set.forEach { expr -> getOrCreateIndex(expr) }
        }
        right.equalitySets.forEach { set ->
            set.forEach { expr -> getOrCreateIndex(expr) }
        }

        // Merge all elements that are equal in both sets
        for (i in equalitySets.indices) {
            val iExpr = equalitySets[i].firstOrNull() ?: continue
            for (j in i + 1 until equalitySets.size) {
                val jExpr = equalitySets[j].firstOrNull() ?: continue
                if (left.areEqual(iExpr, jExpr) && right.areEqual(iExpr, jExpr)) {
                    merge(i, j)
                }
            }
        }

        // Merge less graphs
        for (i in equalitySets.indices) {
            val iExpr = equalitySets[i].firstOrNull() ?: continue
            for (j in i + 1 until equalitySets.size) {
                val jExpr = equalitySets[j].firstOrNull() ?: continue
                // [a,x] < b
                // [b,x] <= a

                // [a] [b] [x]
                // x <= a? true/true
                // x <= b? true/true

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

    private fun dfsIsReachable(from: Int, to: Int, isStrict: Boolean, visited: MutableSet<Int>): Boolean {
        if (from == to)
            return true

        if (from in visited)
            return false

        visited.add(from)
        lessGraph[from]?.forEach { edge ->
            if (isStrict && !edge.isStrict) return@forEach
            if (dfsIsReachable(edge.toIndex, to, isStrict, visited))
                return true
        }

        return false
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
        equalitySets[leftIndex].addAll(equalitySets[rightIndex])
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
            if (set.isEmpty()) {
                set.add(expr)
                return i
            }
        }

        // Allocate a new set
        equalitySets.add(hashSetOf(expr))
        return equalitySets.lastIndex
    }

    private fun tryGetIndex(expr: LogicExpr): Int? {
        return equalitySets.indexOfFirst { it.contains(expr) }.takeIf { it >= 0 }
    }

    data class LessEdge(var toIndex: Int, var isStrict: Boolean)
}