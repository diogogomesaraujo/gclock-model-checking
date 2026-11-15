// -----------------------------------------------------------------

// Utils
// ^^^^^

module utils {
    type Round_t = int

    type Time_t = int

    pure def FirstRound : int = 0

    pure def TimeInit   : int = 0

    type P_Sid_t = int

    pure def InvalidP_Sid : int = -1

    type Flag_t = bool

    pure def One : Flag_t = true

    pure def Zero : Flag_t = false

    type Option_t[a] = Some(a) | None

    type Effects_t[a] = List[a]

    pure def min(a: int, b: int): int =
        if (a < b) a else b
}
