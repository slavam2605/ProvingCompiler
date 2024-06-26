package org.example

import me.alllex.parsus.parser.*
import me.alllex.parsus.token.literalToken
import me.alllex.parsus.token.regexToken

object LanguageParser {
    private fun Grammar<*>.keyword(name: String) = regexToken("$name\\b")

    private suspend fun <R> ParsingScope.required(p: Parser<R>): R {
        return tryParse(p).getOrThrow()
    }

    private fun <R> Parser<R>.required(): Parser<R> {
        val p = this
        return parser { required(p) }
    }

    private val grammar = object : Grammar<List<TopLevel>>() {
        init {
            regexToken("\\s+", ignored = true)
            regexToken("//[^\n\r]*", ignored = true)
            regexToken("/\\*(?s:.)*?\\*/", ignored = true)
        }

        val ifKeyword by keyword("if")
        val elseKeyword by keyword("else")
        val returnKeyword by keyword("return")
        val letKeyword by keyword("let")
        val mutKeyword by keyword("mut")
        val trueKeyword by keyword("true")
        val falseKeyword by keyword("false")
        val funKeyword by keyword("fun")
        val proofKeyword by keyword("proof")
        val axiomKeyword by keyword("axiom")
        val id by regexToken("[a-zA-Z_][a-zA-Z0-9_]*")
        val int by regexToken("[0-9]+")
        val semicolon by literalToken(";").required()
        val leftPar by literalToken("(")
        val rightPar by literalToken(")")
        val leftBrace by literalToken("{")
        val rightBrace by literalToken("}")
        val le by literalToken("<=")
        val lt by literalToken("<")
        val ge by literalToken(">=")
        val gt by literalToken(">")
        val eq by literalToken("==")
        val neq by literalToken("!=")
        val plus by literalToken("+")
        val minus by literalToken("-")
        val star by literalToken("*")
        val slash by literalToken("/")
        val assign by literalToken("=")
        val colon by literalToken(":")
        val excl by literalToken("!")
        val and by literalToken("&&")
        val or by literalToken("||")
        val hash by literalToken("#")
        val arrow by literalToken("->")
        val letEquals by literalToken(":=")
        val comma by literalToken(",")
        val leftSquare by literalToken("[")
        val rightSquare by literalToken("]")
        val dollar by literalToken("$")

        // Tries to parse "-", but fails if it is "->"
        val minusChecked by parser {
            val offset = currentOffset
            if (has(arrow)) {
                fail(UnmatchedToken(minus, offset))
            }
            minus()
            ArithmeticNode.ArithmeticOp.SUB
        }

        // Tries to parser "->", but fails if it is followed by "#"
        val arrowChecked by parser {
            val offset = currentOffset
            val arr = arrow()
            if (has(hash)) {
                fail(UnmatchedToken(arrow, offset))
            }
            arr
        }

        val addSubOp by (plus map { ArithmeticNode.ArithmeticOp.ADD }) or minusChecked

        val mulDivOp by (star map { ArithmeticNode.ArithmeticOp.MUL }) or
                (slash map { ArithmeticNode.ArithmeticOp.DIV })

        val compareOp by (le map { CompareNode.CompareOp.LE }) or
                (lt map { CompareNode.CompareOp.LT }) or
                (ge map { CompareNode.CompareOp.GE }) or
                (gt map { CompareNode.CompareOp.GT }) or
                (eq map { CompareNode.CompareOp.EQ }) or
                (neq map { CompareNode.CompareOp.NEQ })

        val typeExpr by id map { TypeNameNode(it.text, it.offset) }

        val boolExpr by (trueKeyword or falseKeyword) map { BoolNode(it.text, it.offset) }
        val intExpr by int map { IntNode(it.text, it.offset) }
        val nameExpr by (id or dollar) map { NameNode(it.text, it.offset) }
        val bracedExpr by -leftPar * ref(::expr) * -rightPar
        val invocationExpr by nameExpr * leftPar * separated(ref(::expr), comma) * rightPar map { InvocationNode(it.t1, it.t3, it.t1.offset) }
        val term by bracedExpr or boolExpr or intExpr or invocationExpr or nameExpr
        val notExpr: Parser<ExprNode> by (excl * ref(::notExpr) map { NotNode(it.second, it.first.offset) }) or term

        val mulDivExpr by leftAssociative(notExpr, mulDivOp) { l, op, r -> ArithmeticNode(l, r, op, l.offset) }
        val addSubExpr by leftAssociative(mulDivExpr, addSubOp) { l, op, r -> ArithmeticNode(l, r, op, l.offset) }
        val compareExpr by leftAssociative(addSubExpr, compareOp) { l, op, r -> CompareNode(l, r, op, l.offset) }
        val andExpr by leftAssociative(compareExpr, and) { l, _, r -> AndNode(l, r, l.offset) }
        val orExpr by leftAssociative(andExpr, or) { l, _, r -> OrNode(l, r, l.offset) }
        val arrowExpr by rightAssociative(orExpr, arrowChecked) { l, _, r -> ArrowNode(l, r, l.offset) }

        val expr: Parser<ExprNode> by arrowExpr

        val ifStatement by parser {
            val offset = ifKeyword().offset
            val cond = expr()
            val trueOffset = (required(leftBrace)).offset
            val trueBlock = zeroOrMore(statement)()
            required(rightBrace)
            val falseBlock = poll(elseKeyword)?.let {
                val falseOffset = leftBrace().offset
                val lines = zeroOrMore(statement)()
                rightBrace()
                BlockNode(lines, falseOffset)
            }
            IfNode(cond, BlockNode(trueBlock, trueOffset), falseBlock, offset)
        }

        val returnStatement by parser {
            val offset = returnKeyword().offset
            val expr = expr()
            val block = if (has(arrow)) {
                proofBlock()
            } else null
            semicolon()
            ReturnNode(expr, block, offset)
        }

        val letStatement by parser {
            val offset = letKeyword().offset
            val mut = poll(mutKeyword)?.let { true } ?: false
            val name = id()
            val type = poll(colon * typeExpr)?.second
            val init = poll(assign * expr)?.second
            semicolon()
            LetNode(name.text, type, mut, init, name.offset, offset)
        }

        val assignStatement by parser {
            val name = expr()
            assign()
            val expr = expr()
            semicolon()
            AssignNode(name, expr, name.offset)
        }

        val letProofStatement by letKeyword * id * letEquals * expr * semicolon map {
            LetEqualsNode(it.t2.text, it.t4, it.t2.offset, it.t1.offset)
        }

        val deductionBlock: Parser<ProofElement> by parser {
            val offset = hash().offset
            leftSquare()
            val inputs = separated(expr, comma)()
            rightSquare()
            val blockOffset = leftBrace().offset
            val body = zeroOrMore(ref(::proofElement))()
            required(rightBrace)
            DeductionBlockNode(inputs, ProofBlockNode(body, blockOffset), offset)
        }

        val proofElement: Parser<ProofElement> by letProofStatement or
                (expr * semicolon map { it.first }) or
                ref(::proofFunction) or
                deductionBlock

        val proofBlock by hash * leftBrace * zeroOrMore(proofElement) * rightBrace map {
            ProofBlockNode(it.t3, it.t1.offset)
        }

        val compilerCommand by hash * id map { CompilerCommandNode(it.t2.text, it.t1.offset) }

        val statement: Parser<StatementNode> by ifStatement or
                returnStatement or
                letStatement or
                assignStatement or
                proofBlock or
                compilerCommand

        val codeBlock = leftBrace * zeroOrMore(statement) * rightBrace map {
            BlockNode(it.t2, it.t1.offset)
        }

        val functionArgument by id * colon * typeExpr map { ArgumentNode(it.t1.text, it.t3, it.t1.offset) }

        val functionContract by parser(setOf(hash)) {
            val offset = hash().offset
            val inputOffset = leftSquare().offset
            val input = ProofBlockNode(separated(expr, comma)(), inputOffset)
            rightSquare()
            val arrow = poll(arrow)
            val output = arrow?.let {
                val off = leftSquare().offset
                val o = separated(expr, comma)()
                required(rightSquare)
                o to off
            }?.let { ProofBlockNode(it.first, it.second) }
            FunctionContract(input, output, offset)
        }

        val functionDeclaration by parser {
            val contract = poll(functionContract)
            val offset = funKeyword().offset
            val name = id()
            leftPar()
            val arguments = separated(functionArgument, comma)()
            rightPar()
            colon()
            val returnType = typeExpr()
            val body = codeBlock()
            FunctionNode(name.text, contract, arguments, returnType, body, name.offset, offset)
        }

        val proofFunction by parser {
            val contract = poll(functionContract)
            val offset = proofKeyword().offset
            val name = id()
            leftPar()
            val arguments = separated(functionArgument, comma)()
            rightPar()
            val blockOffset = leftBrace().offset
            val elements = zeroOrMore(proofElement)()
            rightBrace()
            ProofFunctionNode(name.text, contract, arguments, ProofBlockNode(elements, blockOffset), name.offset, offset)
        }

        val axiomDeclaration by parser {
            val offset = axiomKeyword().offset
            val name = poll(id)?.text
            required(leftPar)
            val arguments = required(separated(functionArgument, comma))
            required(rightPar)
            val blockOffset = required(leftBrace).offset
            val body = required(zeroOrMore(proofElement))
            required(rightBrace)
            AxiomNode(name, arguments, ProofBlockNode(body, blockOffset), offset)
        }

        val topLevel: Parser<TopLevel> by functionDeclaration or axiomDeclaration

        override val root by zeroOrMore(topLevel)
    }

    fun parse(input: String): List<TopLevel>? {
        try {
            return when (val result = grammar.parse(input)) {
                is ParsedValue -> result.value
                else -> {
                    System.err.println(result)
                    null
                }
            }
        } catch (e: ParseException) {
            System.err.println(e.error)
            return null
        }
    }
}