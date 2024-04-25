package org.example

fun main() {
    val input = """
        let a: int;
        let b: int;
        let x: int;
        if a < b {
            x = a;
            #facts
        } else {
            x = b;
            #facts
        }
        #facts
        #{ x <= a; x <= b; }
    """.trimIndent()
    // TODO add int value to equality sets to check with other ints
    // TODO support functions
    // TODO support contracts for arguments and return values like #{ $ <= a; $ <= b; }
    // TODO support modus ponens and logic axioms
    // TODO support compilation

    val value = LanguageParser.parse(input) ?: return
    LanguageResolver(input).resolveBlock(value)
}