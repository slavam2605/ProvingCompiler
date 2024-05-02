package org.example.output

object ANSIColors {
    private const val ESCAPE = '\u001b'
    private const val RESET = "$ESCAPE[0m"
    private const val BG_JUMP = 10

    enum class Color(val baseCode: Int) {
        BLACK(30),
        RED(31),
        GREEN(32),
        YELLOW(33),
        BLUE(34),
        MAGENTA(35),
        CYAN(36),
        LIGHT_GRAY(37),

        DARK_GRAY(90),
        LIGHT_RED(91),
        LIGHT_GREEN(92),
        LIGHT_YELLOW(93),
        LIGHT_BLUE(94),
        LIGHT_MAGENTA(95),
        LIGHT_CYAN(96),
        WHITE(97);

        val backgroundCode: Int = baseCode + BG_JUMP
    }

    enum class Mode(val code: Int) {
        BOLD(1),
        DIM(2),
        ITALIC(3),
        UNDERSCORE(4),
        BLINK(5),
        REVERSE(7),
        CONCEALED(8)
    }

    fun applyStyle(s: String, foreground: Color?, background: Color?, mode: Mode?): String {
        val styles = listOfNotNull(
            foreground?.let { "${it.baseCode}" },
            background?.let { "${it.backgroundCode}" },
            mode?.let { "${it.code}" }
        ).ifEmpty { listOf("0") }.joinToString(separator = ";")
        return "$ESCAPE[${styles}m$s$RESET"
    }

    data class Style(val foreground: Color? = null, val background: Color? = null, val mode: Mode? = null) {
        operator fun invoke(s: String) = applyStyle(s, foreground, background, mode)
    }
}

