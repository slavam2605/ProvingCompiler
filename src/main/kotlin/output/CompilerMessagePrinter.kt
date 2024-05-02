package org.example.output

import org.example.LanguageResolver
import java.io.PrintStream

class CompilerMessagePrinter(private val input: String) {
    internal val contextStack = mutableListOf<LanguageResolver.ErrorContext>()
    
    private val stream: PrintStream
        get() = System.err

    internal inline fun <T> withContext(context: LanguageResolver.ErrorContext, block: () -> T): T {
        contextStack.add(context)
        try {
            return block()
        } finally {
            check(context === contextStack.removeLast())
        }
    }

    fun printError(offset: Int, error: String?, hint: String, last: Boolean = true) {
        printBlock(offset, error, hint)
        contextStack.asReversed().forEach { context ->
            printBlock(context.offset, null, "from here")
        }
        if (last) {
            newLineError()
        }
    }

    private fun printBlock(offset: Int, error: String?, hint: String) {
        if (offset < 0) {
            stream.println("error: $error")
            return
        }

        val lineStart = input.substring(0, offset).indexOfLast { it == LINE_BREAK_CHAR } + 1
        val line = input.substring(lineStart).takeWhile { it != LINE_BREAK_CHAR }

        val lineNumber = getLineNumber(offset)
        val col = offset - lineStart

        if (error != null) {
            stream.println(ERROR("error") + TITLE(": $error"))
        }
        val lineNumberString = "${lineNumber + 1}"
        val pad = " ".repeat(lineNumberString.length)

        stream.println(GUTTER("$pad-->") + " file:${lineNumber + 1}:${col + 1}")
        stream.println(GUTTER("$pad |"))
        stream.println(GUTTER("${lineNumber + 1} |") + "\t$line")
        stream.println(GUTTER("$pad |") + "\t${" ".repeat(col)}" + ERROR("^ $hint"))
    }

    fun printRedeclarationError(offset: Int, name: String, existingSymbol: LanguageResolver.ResolvedSymbol) {
        printError(offset, "Symbol '${name}' is already defined in this scope", "redeclaration", false)
        when (existingSymbol) {
            is LanguageResolver.ResolvedSymbol.Function -> {
                printError(existingSymbol.node.nameOffset, null, "previous function declaration", false)
            }
            is LanguageResolver.ResolvedSymbol.ProofFunction -> {
                printError(existingSymbol.node.offset, null, "previous proof declaration", false)
            }
            is LanguageResolver.ResolvedSymbol.LocalVariable -> {
                printError(existingSymbol.node.nameOffset, null, "previous variable declaration", false)
            }
            is LanguageResolver.ResolvedSymbol.LetAlias -> {
                printError(existingSymbol.node.nameOffset, null, "previous proof-let declaration", false)
            }
            is LanguageResolver.ResolvedSymbol.FunctionArgument -> {
                printError(existingSymbol.node.offset, null, "previous argument declaration", false)
            }
            is LanguageResolver.ResolvedSymbol.PatternName -> {
                error("Unexpected symbol type: PatternName must only appear in axiom patterns")
            }
        }
        newLineError()
    }

    fun printInformation(offset: Int, message: String) {
        if (offset < 0) {
            stream.println(message)
        }

        val lineStart = input.substring(0, offset).indexOfLast { it == LINE_BREAK_CHAR } + 1
        val col = offset - lineStart
        val lineNumber = getLineNumber(offset)

        stream.println(INFO("info") + TITLE(": $message"))
        stream.println(GUTTER("\t-->") + " file:${lineNumber + 1}:${col + 1}")
    }

    private fun getLineNumber(offset: Int) =
        input.substring(0, offset).count { it == LINE_BREAK_CHAR }

    private fun newLineError() {
        stream.println()
    }

    companion object {
        private const val LINE_BREAK_CHAR = '\n'
        private val ERROR = ANSIColors.Style(foreground = ANSIColors.Color.RED, mode = ANSIColors.Mode.BOLD)
        private val TITLE = ANSIColors.Style(mode = ANSIColors.Mode.BOLD)
        private val GUTTER = ANSIColors.Style(foreground = ANSIColors.Color.BLUE, mode = ANSIColors.Mode.BOLD)
        private val INFO = ANSIColors.Style(foreground = ANSIColors.Color.CYAN, mode = ANSIColors.Mode.BOLD)
    }
}