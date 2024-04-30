package org.example

fun main() {
    val input = """
        #[] -> [$ -> a <= b;]
        fun isLessOrEquals(a: int, b: int): bool {
            if a <= b {
                let x: bool = true;
                #{
                    a <= b -> x -> a <= b;
                    a <= b;
                    x -> a <= b;
                }
                return x;
            }
            let x: bool = false;
            #{
                !x;
                !x -> !!x -> a <= b;
                !!x -> a <= b;
                x -> !!x;
                (x -> !!x) -> (!!x -> a <= b) -> x -> a <= b;
                (!!x -> a <= b) -> x -> a <= b;
                x -> a <= b;
            }
            return x;
        }

        #[] -> [$ -> a < b;]
        fun isLess(a: int, b: int): bool {
            if a == b {
                return false;
            }
            return isLessOrEquals(a, b) -> #{
                !(a == b) -> a <= b -> a < b;
                a <= b -> a < b;
                ($ -> a <= b) -> (a <= b -> a < b) -> $ -> a < b;
                (a <= b -> a < b) -> $ -> a < b;
                $ -> a < b;
            };
        }
    """.trimIndent()

    // TODO support compilation

    val value = LanguageParser.parse(input) ?: return
    LanguageResolver(input).resolveFile(value)
}