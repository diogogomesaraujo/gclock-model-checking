// -----------------------------------------------------------------

// Time properties
// ^^^^^^^^^^^^^^^

module time {
    import utils.* from "./utils"
    import assumptions.* from "./assumptions"
    import logs.* from "./logs"

    // -----------------------------------------------------------------

    // G-Clock
    // ^^^^^^^

    // Property 1 (Time Agreement): If two parties query the time and no OK requests have been sent
    // in the middle then G-clock responds with the same time.
    pure def TimeAgreementOn(ls : Set[EnvSimLog_t]) : bool =
        ls.forall(l1 =>
            match l1.log {
                | LogPRound(r1) => {
                    ls.forall(l2 =>
                        match l2.log {
                            | LogPRound(r2) =>
                                (l2.index > l1.index) implies {
                                    val no_ok_between = ls.forall(lm =>
                                        and { lm.index > l1.index, lm.index < l2.index } implies {
                                            match lm.log {
                                                | LogRoundOk(_) => false
                                                | _             => true
                                            }
                                        }
                                    )

                                    no_ok_between implies {
                                        r1.round == r2.round
                                    }
                                }
                            | _ => true
                        }
                    )
                }
                | _ => true
            }
        )

    // Property 2 (Time Liveness): If all registered honest parties are ready, then time advances.
    // this is non-trivial since we have to track who was registered and corrupted at all times
    pure def TimeLivenessOn(ls : Set[EnvSimLog_t]) : bool =
        ls.forall(l2 =>
            ls.forall(l1 =>
                (l1.index + 1 == l2.index) implies
                match l2.log {
                    | LogRoundOk(p) => {
                        val honest = l2.reg.exclude(l2.c)
                        val all_ready = and {
                            honest.size() > 0,
                            honest.forall(q => l2.ok.contains(q) or q == p),
                        }
                        all_ready implies (l2.round == min(l1.round + 1, MaxRound))
                    }
                    | _ => true
                }
            )
        )

    // Property 3 (Time Soundness): If time advanced then all currently registered honest parties were ready.
    pure def TimeSoundnessOn(ls : Set[EnvSimLog_t]) : bool =
        ls.forall(l2 =>
            ls.forall(l1 =>
                and { l1.index + 1 == l2.index, l2.round > l1.round } implies
                match l2.log {
                    | LogRoundOk(p) => {
                        val honest = l2.reg.exclude(l2.c)
                        val all_ready = and {
                            honest.size() > 0,
                            honest.forall(q => l2.ok.contains(q) or q == p),
                        }
                        and {
                            all_ready,
                            l2.round == l1.round + 1,
                            l2.ok.exclude(l2.c) == Set(),
                        }
                    }
                    | _ => false
                }
            )
        )

    // -----------------------------------------------------------------

    // G-Slot
    // ^^^^^^

    pure def SlotWithinOn(ls : Set[EnvSimLog_t], bound : int, ahead : int) : bool =
            ls.forall(l =>
                match l.log {
                    | LogPRound(r) => or { l.c.contains(r.p_sid)
                                         , and { r.round <= l.round + ahead, r.round + bound >= l.round } }
                    | _            => true
                }
            )
}
