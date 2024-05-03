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

sealed class ExprNode(offset: Int) : AstNode(offset), ProofElement
sealed class StatementNode(offset: Int) : AstNode(offset)
sealed class TypeExprNode(offset: Int) : AstNode(offset)
interface ProofElement
interface TopLevel

class FunctionNode(val name: String, val contract: FunctionContract?, val arguments: List<ArgumentNode>,
                   val returnType: TypeExprNode, val body: BlockNode, val nameOffset: Int, offset: Int) : AstNode(offset), TopLevel

class ArgumentNode(val name: String, val type: TypeExprNode, offset: Int) : AstNode(offset)

class FunctionContract(val input: ProofBlockNode, val output: ProofBlockNode?, offset: Int) : AstNode(offset)

// =============== Proofs ===============

class DeductionBlockNode(val inputs: List<ExprNode>, val body: ProofBlockNode, offset: Int) : AstNode(offset), ProofElement

class LetEqualsNode(val name: String, val expr: ExprNode, val nameOffset: Int, offset: Int) : AstNode(offset), ProofElement

class ProofFunctionNode(val name: String, val contract: FunctionContract?, val arguments: List<ArgumentNode>,
                        val body: ProofBlockNode, val nameOffset: Int, offset: Int) : AstNode(offset), ProofElement

class AxiomNode(val name: String?, val arguments: List<ArgumentNode>, val body: ProofBlockNode, offset: Int) : AstNode(offset), TopLevel

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
            EQ, NEQ -> this
        }

        fun negate(): CompareOp = when (this) {
            LT -> GE
            LE -> GT
            GT -> LE
            GE -> LT
            EQ -> NEQ
            NEQ -> EQ
        }

        fun weaken(): CompareOp? = when (this) {
            LT -> LE
            GT -> GE
            LE, GE, EQ, NEQ -> null
        }

        override fun toString() = str
    }
}

class ArrowNode(val left: ExprNode, val right: ExprNode, offset: Int) : ExprNode(offset)

class OrNode(val left: ExprNode, val right: ExprNode, offset: Int) : ExprNode(offset)

class AndNode(val left: ExprNode, val right: ExprNode, offset: Int) : ExprNode(offset)

class NotNode(val expr: ExprNode, offset: Int) : ExprNode(offset)

class InvocationNode(val expr: ExprNode, val arguments: List<ExprNode>, offset: Int) : ExprNode(offset)

class NameNode(val name: String, offset: Int) : ExprNode(offset)

class IntNode(val value: String, offset: Int) : ExprNode(offset)

class BoolNode(val value: String, offset: Int) : ExprNode(offset)

// =============== Statements ===============

class AssignNode(val name: ExprNode, val expr: ExprNode, offset: Int) : StatementNode(offset)

class LetNode(val name: String, val type: TypeExprNode?, val isMut: Boolean, val initExpr: ExprNode?, val nameOffset: Int, offset: Int) : StatementNode(offset)

class IfNode(val cond: ExprNode, val trueBlock: BlockNode, val falseBlock: BlockNode?, offset: Int) : StatementNode(offset)

class ReturnNode(val expr: ExprNode, val proofBlock: ProofBlockNode?, offset: Int) : StatementNode(offset)

class BlockNode(val lines: List<StatementNode>, offset: Int) : StatementNode(offset)

class ProofBlockNode(val exprList: List<ProofElement>, offset: Int) : StatementNode(offset)

class CompilerCommandNode(val name: String, offset: Int) : StatementNode(offset)

// =============== Type expressions ===============

class TypeNameNode(val name: String, offset: Int) : TypeExprNode(offset)

// =============== Utils ===============

fun ExprNode.transform(block: (ExprNode) -> ExprNode?): ExprNode {
    block(this)?.let { return it }
    return when (this) {
        is ArrowNode -> ArrowNode(left.transform(block), right.transform(block), offset)
        is OrNode -> OrNode(left.transform(block), right.transform(block), offset)
        is AndNode -> AndNode(left.transform(block), right.transform(block), offset)
        is CompareNode -> CompareNode(left.transform(block), right.transform(block), op, offset)
        is ArithmeticNode -> ArithmeticNode(left.transform(block), right.transform(block), op, offset)
        is NotNode -> NotNode(expr.transform(block), offset)
        is InvocationNode -> InvocationNode(expr.transform(block), arguments.map { it.transform(block) }, offset)
        is NameNode, is BoolNode, is IntNode -> this
    }
}