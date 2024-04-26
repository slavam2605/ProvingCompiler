package org.example

sealed class AstNode(val offset: Int) {
    private val contextMap = mutableMapOf<String, Any?>()

    operator fun <T> get(key: ContextKey<T>): T? {
        @Suppress("UNCHECKED_CAST")
        return contextMap[key.key]?.let { it as T }
    }

    operator fun <T> set(key: ContextKey<T>, value: T?) {
        contextMap[key.key] = value
    }

    class ContextKey<@Suppress("unused") T>(val key: String)
}

sealed class ExprNode(offset: Int) : AstNode(offset)
sealed class StatementNode(offset: Int) : AstNode(offset)
sealed class TypeExprNode(offset: Int) : AstNode(offset)

// =============== Expressions ===============

class ArithmeticNode(val left: ExprNode, val right: ExprNode, val op: ArithmeticOp, offset: Int) : ExprNode(offset) {
    enum class ArithmeticOp(private val str: String) {
        ADD("+"), SUB("-"), MUL("*"), DIV("/");

        override fun toString() = str
    }
}

class CompareNode(val left: ExprNode, val right: ExprNode, val op: CompareOp, offset: Int) : ExprNode(offset) {
    enum class CompareOp(private val str: String) {
        LT("<"), LE("<="), GT(">"), GE(">="), EQ("=="), NEQ("!=");

        fun flip(): CompareOp = when (this) {
            LT -> GT
            LE -> GE
            GT -> LT
            GE -> LE
            EQ -> EQ
            NEQ -> NEQ
        }

        fun negate(): CompareOp = when (this) {
            LT -> GE
            LE -> GT
            GT -> LE
            GE -> LT
            EQ -> NEQ
            NEQ -> EQ
        }

        override fun toString() = str
    }
}

class OrNode(val left: ExprNode, val right: ExprNode, offset: Int) : ExprNode(offset)

class AndNode(val left: ExprNode, val right: ExprNode, offset: Int) : ExprNode(offset)

class NotNode(val expr: ExprNode, offset: Int) : ExprNode(offset)

class NameNode(val name: String, offset: Int) : ExprNode(offset)

class IntNode(val value: String, offset: Int) : ExprNode(offset)

class BoolNode(val value: String, offset: Int) : ExprNode(offset)

// =============== Statements ===============

class AssignNode(val name: ExprNode, val expr: ExprNode, offset: Int) : StatementNode(offset)

class LetNode(val name: String, val type: TypeExprNode?, val isMut: Boolean, val initExpr: ExprNode?, val nameOffset: Int, offset: Int) : StatementNode(offset)

class IfNode(val cond: ExprNode, val trueBlock: BlockNode, val falseBlock: BlockNode?, offset: Int) : StatementNode(offset)

class ReturnNode(val expr: ExprNode, offset: Int) : StatementNode(offset)

class BlockNode(val lines: List<StatementNode>, offset: Int) : StatementNode(offset)

class ProofBlockNode(val exprList: List<ExprNode>, offset: Int) : StatementNode(offset)

class CompilerCommandNode(val name: String, offset: Int) : StatementNode(offset)

// =============== Type expressions ===============

class TypeNameNode(val name: String, offset: Int) : TypeExprNode(offset)