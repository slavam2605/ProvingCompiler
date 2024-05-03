package org.example

fun main() {
    val input = """
        #[] -> [$ -> !a || !b]
        fun and(a: bool, b: bool): bool {
            return !(a && b);
        }
    """.trimIndent()

    val axioms = LanguageResolver::class.java.getResource("/axioms.lang")?.readText()
        ?: error("Failed to load resource: axioms.lang")
    val languageResolver = LanguageResolver()
    LanguageParser.parse(axioms)?.let {
        if (!languageResolver.resolveFile(axioms, it))
            error("Failed to load axioms")
    }

    // TODO support compilation

    val value = LanguageParser.parse(input) ?: return
    if (!languageResolver.resolveFile(input, value))
        System.err.println("Compilation failed")
}