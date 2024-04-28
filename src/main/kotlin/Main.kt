package org.example

fun main() {
    val input = """
        let a: int;
        let x: int;
        if a < 100 {
            x = a;
            #facts
        } else {
            x = 0;
            #facts
        }
        #facts
        #{ x != 50; }
    """.trimIndent()

    // TODO support functions
    // TODO support compilation

    val value = LanguageParser.parse(input) ?: return
    LanguageResolver(input).resolveFile(value)
}