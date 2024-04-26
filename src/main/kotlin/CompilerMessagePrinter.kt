package org.example

class CompilerMessagePrinter(private val input: String) {
    fun printError(offset: Int, error: String?, hint: String, last: Boolean = true) {
        if (offset < 0) {
            System.err.println("error: $error")
            return
        }

        val lineStart = input.substring(0, offset).indexOfLast { it == LINE_BREAK_CHAR } + 1
        val line = input.substring(lineStart).takeWhile { it != LINE_BREAK_CHAR }

        val lineNumber = getLineNumber(offset)
        val col = offset - lineStart

        if (error != null) {
            System.err.println("error: $error")
        }
        System.err.println("\t--> file:${lineNumber + 1}:${col + 1}")
        System.err.println(" \t|")
        System.err.println("${lineNumber + 1}\t|\t$line")
        System.err.println(" \t|\t${" ".repeat(col)}^ $hint")
        if (last) {
            newLineError()
        }
    }

    fun printInformation(offset: Int, message: String) {
        if (offset < 0) {
            println(message)
        }

        val lineNumber = getLineNumber(offset)
        println("Line $lineNumber: $message")
    }

    private fun getLineNumber(offset: Int) =
        input.substring(0, offset).count { it == LINE_BREAK_CHAR }

    fun newLineError() {
        System.err.println()
    }

    companion object {
        private const val LINE_BREAK_CHAR = '\n'
    }
}