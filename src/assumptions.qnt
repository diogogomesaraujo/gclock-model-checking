// -----------------------------------------------------------------

// Assumptions
// ^^^^^^^^^^^

module assumptions {
    // Common
    pure val NumberOfParties = 2

    pure val Corrupted       = Set()

    pure val MaxRound        = 2

    pure val TapeSize        = 1

    pure val LogsSize        = 5

    pure val RoundDuration   = 2   // T

    // Real world (Relative Time protocol) and G-Slot
    pure val Delta           = 1   // network delay ∆ (in slots) of F_DDiffuse

    pure val MaxDrift        = 1   // bound on Σ ∈ ℕ; Theorem 7 needs Σ < RoundDuration (use RoundDuration = 2)

    pure val SampleSize      = 1   // n: blocks collected before running the median algorithm

    pure val InboxSize       = 1   // bound on pending messages per F_DDiffuse instance

    // Theorem 7: the relative time protocol realizes G_Slot with Θ = ∆ + 1.
    pure val Theta           = Delta + 1
}
