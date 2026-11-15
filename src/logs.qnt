// -----------------------------------------------------------------

// Logs
// ^^^^
//
// Z observes the same kind of log in every world.

module logs {
    import utils.* from "./utils"
    import assumptions.* from "./assumptions"

    type Log_t = LogRegOk(P_Sid_t)
               | LogReg(P_Sid_t)
               | LogRoundOk(P_Sid_t)
               | LogFailed(P_Sid_t)
               | LogPRound({ p_sid : P_Sid_t, round : Round_t })
               | LogSRound(Round_t)

    // round = current round (G-Clock) / real slot (G-Slot, real world)
    type EnvSimLog_t = {
        index : int,
        log   : Log_t,
        reg   : Set[P_Sid_t],
        c     : Set[P_Sid_t],
        ok    : Set[P_Sid_t],
        round : Round_t
    }

    pure def EnvSimNewLog(log : Log_t, index : int, reg : Set[P_Sid_t], c : Set[P_Sid_t], ok : Set[P_Sid_t], round : Round_t) : EnvSimLog_t =
        { index : index, log : log, reg : reg, c : c, ok : ok, round : round }

    // keeps the last LogsSize logs
    pure def EnvSimLogPush(logs : Set[EnvSimLog_t], l : Log_t, reg : Set[P_Sid_t], c : Set[P_Sid_t], ok : Set[P_Sid_t], round : Round_t) : Set[EnvSimLog_t] =
        if (size(logs) >= LogsSize) {
            val kept = logs.filter(x => x.index > 0)
                           .map(x => { index: x.index - 1, log : x.log, reg : x.reg, c : x.c, ok : x.ok, round : x.round })
            kept.union(Set(EnvSimNewLog(l, size(kept), reg, c, ok, round)))
        } else {
            logs.union(Set(EnvSimNewLog(l, size(logs), reg, c, ok, round)))
        }
}
