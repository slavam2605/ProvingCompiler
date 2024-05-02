package org.example

fun main() {
    val input = """
        #[] -> [$ <= a, $ <= b, $ <= c]
        fun min(a: int, b: int, c: int): int {
            if a <= b && a <= c {
                return a;
            }
            if b <= a && b <= c {
                return b;
            }
            #facts
            #{
//                !(a <= b && a <= c);
//                !(b <= a && b <= c);

                #[!(a <= b && a <= c)] -> [a <= c -> a > b]
                proof p1(a: int, b: int, c: int) {
                    let x := a <= b;
                    let y := a <= c;
                    !(x && y) -> !x || !y;
                    !x || !y;
                    !x || !y -> !y || !x;
                    !y || !x;
                    (!y || !x) -> !!y -> !x;
                    !!y -> !x;
                    y -> !!y;
                    (y -> !!y) -> (!!y -> !x) -> y -> !x;
                    y -> !x;
                    !(a <= b) -> a > b;
                    (y -> !x) -> (!(a <= b) -> a > b) -> y -> a > b;
                    a <= c -> a > b;
                }

                p1(a, b, c); // a <= c -> a > b
                p1(b, a, c); // b <= c -> b > a
                 
                #[a <= c -> a > b, b <= c -> b > a] -> [a > c]
                proof p2(a: int, b: int, c: int) {
                    (a <= c -> a > b) -> a <= c -> a <= c && a > b;
                    a <= c -> a <= c && a > b;
                    a <= c && a > b -> b < c;
                    (a <= c -> a <= c && a > b) -> (a <= c && a > b -> b < c) -> a <= c -> b < c;
                    a <= c -> b < c;
                    b < c -> b <= c;
                    (a <= c -> b < c) -> (b < c -> b <= c) -> a <= c -> b <= c;
                    a <= c -> b <= c;
                    (a <= c -> b <= c) -> (b <= c -> b > a) -> a <= c -> b > a;
                    a <= c -> b > a;
                    (a <= c -> a > b) -> (a <= c -> b > a) -> a <= c -> a > b && b > a;
                    a <= c -> a > b && b > a;
                    a > b && b > a -> false;
                    (a <= c -> a > b && b > a) -> (a > b && b > a -> false) -> a <= c -> false;
                    a <= c -> false;
                    (a <= c -> false) -> !(a <= c);
                    !(a <= c);
                    !(a <= c) -> a > c;
                    a > c;
                }
                
                p2(a, b, c); // a > c
                p2(b, a, c); // b > c
            }
            return c;
        }
    """.trimIndent()

    // TODO support compilation

    val value = LanguageParser.parse(input) ?: return
    if (!LanguageResolver(input).resolveFile(value))
        System.err.println("Compilation failed")
}