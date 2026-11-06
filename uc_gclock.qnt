// Model Checking G-Clock
// from: https://eprint.iacr.org/2026/292.pdf

// -----------------------------------------------------------------

// Assumptions
// ^^^^^^^^^^^

module assumptions {
    pure val NumberOfParties = 2

    pure val Corrupted       = Set(1)

    pure val MaxRound        = 5

    pure val TapeSize        = 1

    pure val LogsSize        = 10
}

// Utils
// ^^^^^
//
module utils {
    type Round_t = int

    pure def FirstRound : int = 0

    // ^^^^^

    type P_Sid_t = int

    type Sid_t = ZS_Sid | P_Sid(P_Sid_t) | GClock_Sid

    pure def InvalidP_Sid : int = -1

    // ^^^^^

    type Flag_t = bool

    pure def One : Flag_t = true

    pure def Zero : Flag_t = false

    // ^^^^^

    type Option_t[a] = Some(a) | None

    // ^^^^^

    type Effects_t[a] = List[a]

    // ^^^^^

    pure def min(a: int, b: int): int = if (a < b) a else b
}

// UC Framework
// ^^^^^^^^^^^^

module uc {
    import utils.*
    import assumptions.*

    type ITM[in, out, in_msg] = {
        sid                : Sid_t,
        input              : List[in],
        output             : List[out],
        incoming_messages  : List[in_msg],
    }

    type ItmEffect[in, out, in_msg] = ItmEffectUpdateInput(in)
                                    | ItmEffectUpdateOutput(out)
                                    | ItmEffectUpdateIncoming(in_msg)
                                    | ItmEffectPopInput
                                    | ItmEffectPopOutput
                                    | ItmEffectPopIncoming

    pure def ItmInit(sid: Sid_t) : ITM[in, out, incoming] = {
        sid               : sid,
        input             : [],
        output            : [],
        incoming_messages : [],
    }

    pure def PopTape(tape : List[a]) : List[a] = {
        if (length(tape) == 0) tape else tape.tail()
    }

    pure def ItmApplyEffect(itm : ITM[in, out, incoming], effect : ItmEffect[in, out, incoming]) : ITM[in, out, incoming] = {
        match (effect) {
            | ItmEffectUpdateInput(msg)    => itm.with("input", itm.input.append(msg))
            | ItmEffectUpdateOutput(msg)   => itm.with("output", itm.output.append(msg))
            | ItmEffectUpdateIncoming(msg) => itm.with("incoming_messages", itm.incoming_messages.append(msg))
            | ItmEffectPopInput            => itm.with("input", PopTape(itm.input))
            | ItmEffectPopOutput           => itm.with("output", PopTape(itm.output))
            | ItmEffectPopIncoming         => itm.with("incoming_messages", PopTape(itm.incoming_messages))
        }
    }

    pure def ReadNew(tape : List[a]) : Option_t[a] = {
        if (length(tape) == 0) None
        else Some(tape.head())
    }

    pure def ReadNewInput(itm) = {
        ReadNew(itm.input)
    }

    pure def ReadNewOutput(itm) = {
        ReadNew(itm.output)
    }

    pure def ReadNewIncoming(itm) = {
        ReadNew(itm.incoming_messages)
    }

    pure def ItmIsEmpty(itm : ITM[in, out, incoming]) : bool = {
        and {
            length(itm.input) == 0,
            length(itm.output) == 0,
            length(itm.incoming_messages) == 0,
        }
    }

    pure def ItmFits(itm : ITM[in, out, incoming]) : bool = {
        and {
            length(itm.input) <= TapeSize,
            length(itm.output) <= TapeSize,
            length(itm.incoming_messages) <= TapeSize,
        }
    }
}

// -----------------------------------------------------------------

// Ideal-world Model
// ^^^^^^^^^^^^^^^^

module iw {
    import uc.*
    import utils.*
    import assumptions.*

    // -----------------------------------------------------------------

    // Globals
    // ^^^^^^^

    var Iw_ZS        : IwEnvSimState
    var Iw_GClock   : IwClockState
    var Iw_Parties  : IwPartiesState

    // Set when a step needed more than TapeSize slots on some tape.
    var Iw_overflow : bool

    // -----------------------------------------------------------------

    // Log
    // ^^^

    type IwLog = IwLogRegOk(P_Sid_t)
               | IwLogReg(P_Sid_t)
               | IwLogRoundOk(P_Sid_t)
               | IwLogFailed(P_Sid_t)
               | IwLogPRound({ p_sid : P_Sid_t, round: Round_t })
               | IwLogSRound(Round_t)

    // -----------------------------------------------------------------

    // Effect
    // ^^^^^^^

    type IwEffect = GClockIwEffect(IwClockEffect)
                  | EnvSimIwEffect(IwEnvSimEffect)
                  | PartiesIwEffect(IwPartiesEffect)

    type IwWorld = {
        zs : IwEnvSimState,
        g : IwClockState,
        p : IwPartiesState,
    }

    pure def IwApplyEffect(w : IwWorld, e : IwEffect) : IwWorld = {
        match e {
            | EnvSimIwEffect(x)      => w.with("zs", IwEnvSimApplyEffect(w.zs, x))
            | GClockIwEffect(x)      => w.with("g", IwClockApplyEffect(w.g, x))
            | PartiesIwEffect(x)     => w.with("p", IwPartiesApplyEffect(w.p, x))
        }
    }

    pure def IwWorldFits(w : IwWorld) : bool = {
        and {
            ItmFits(w.g.itm),
            w.p.keys().forall(k => ItmFits(w.p.get(k).itm)),
        }
    }

    pure def IwStayIdle(g : IwClockState, p : IwPartiesState) : bool = {
        and {
            ItmIsEmpty(g.itm),
            p.keys().forall(k => ItmIsEmpty(p.get(k).itm)),
        }
    }

    // -----------------------------------------------------------------

    // GClock
    // ^^^^^^

    type IwClockInput = IwClockInputReg(P_Sid_t)   // in the paper Psid.Reg()
                      | IwClockInputRound(P_Sid_t) // in the paper Psid.Round()
                      | IwClockInputOk(P_Sid_t)    // in the paper Psid.OK()

    type IwClockOutput = ()

    type IwClockIncoming = IwClockIncomingRound             // in the paper Sim.Round() but adapted to the real world model
                         | IwClockIncomingCorrupt(P_Sid_t)  // modelling corruptions like Universally Composable Synchronous Computation instead

    type IwClockITM = ITM[IwClockInput, IwClockOutput, IwClockIncoming]

    type IwClockState = {
        itm                : IwClockITM,
        current_round      : Round_t,          // in the paper r
        registered_parties : Set[P_Sid_t],     // in the paper Reg
        corrupted_parties  : Set[P_Sid_t],     // in the paper C
        done               : P_Sid_t -> Flag_t // in the paper Done
    }

    type IwClockAction = IwClockActionRdInput | IwClockActionRdIncoming

    type IwClockEffect = IwClockEffectUpdateItm(ItmEffect[IwClockInput, IwClockOutput, IwClockIncoming])
                     | IwClockEffectIncrementRound
                     | IwClockEffectUpdateRegistered(P_Sid_t)
                     | IwClockEffectUpdateCorrupted(P_Sid_t)
                     | IwClockEffectUpdateDone({ p_sid : P_Sid_t, flag : Flag_t })

    pure def IwClockApplyEffect(state : IwClockState, effect : IwClockEffect) : IwClockState = {
        match (effect) {
            | IwClockEffectUpdateItm(e)            => state.with("itm", ItmApplyEffect(state.itm, e))
            | IwClockEffectUpdateRegistered(p_sid) => state.with("registered_parties", state.registered_parties.union(Set(p_sid)))
            | IwClockEffectUpdateCorrupted(p_sid)  => state.with("corrupted_parties", state.corrupted_parties.union(Set(p_sid)))
            | IwClockEffectUpdateDone(d)           => state.with("done", state.done.put(d.p_sid, d.flag))
            | IwClockEffectIncrementRound          => state.with("current_round", if (state.current_round < MaxRound) state.current_round + 1 else MaxRound) // saturates at MaxRound so the state space is finite
        }
    }

    pure def IwClockCreateEnvSimLog(state : IwClockState, log : IwLog) : IwEffect =
        EnvSimIwEffect(IwEnvSimEffectLog({
            log   : log,
            reg   : state.registered_parties,
            c     : state.corrupted_parties,
            ok    : state.done.keys().fold(Set(), (acc, d) =>
                        if (state.done.get(d) == One) acc.union(Set(d))
                        else acc
                    ),
            round : state.current_round
        } ))

    pure def IwClockInit : IwClockState = {
        itm                : ItmInit(GClock_Sid),
        current_round      : FirstRound,
        registered_parties : Set(),
        corrupted_parties  : Corrupted,
        done               : Map()
    }

    pure def IwClockRegister(clock : IwClockState, p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        val effects = [GClockIwEffect(IwClockEffectUpdateRegistered(p_sid))]
        if (clock.registered_parties.contains(p_sid)) {
            effects
                .append(PartiesIwEffect(IwPartiesEffectUpdateItm({p_sid : p_sid, effect : ItmEffectUpdateOutput(IwPartiesOutputRegisterOk)})))
        }
        else {
            effects
                .append(GClockIwEffect(IwClockEffectUpdateDone({ p_sid : p_sid, flag: Zero })))
                .append(PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectUpdateOutput(IwPartiesOutputRegisterOk) })))
        }
    }

    pure def IwClockPartyRound(clock : IwClockState, p_sid: P_Sid_t) : Effects_t[IwEffect] = {
        [PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectUpdateOutput(IwPartiesOutputRound(clock.current_round)) }))]
    }

    pure def IwClockSimulatorRound(clock : IwClockState) : Effects_t[IwEffect] = {
        [IwClockCreateEnvSimLog(clock, IwLogSRound(clock.current_round))]
    }

    pure def IwClockOk(clock : IwClockState, p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        if (not(clock.registered_parties.contains(p_sid))) {
            [PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectUpdateOutput(IwPartiesOutputFailed) }))]
        } else {
        if (not((clock.registered_parties.exclude(clock.corrupted_parties))
                    .exists(sid => clock.done.put(p_sid, One).get(sid) == Zero)))
            clock.done.keys().exclude(clock.corrupted_parties).fold([], (acc, k) =>
                    acc.append(GClockIwEffect(IwClockEffectUpdateDone({ p_sid : k, flag : Zero }))))
                       .append(GClockIwEffect(IwClockEffectIncrementRound))
                       .append(PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid : p_sid
                                                                        , effect : ItmEffectUpdateOutput(IwPartiesOutputRoundOk) })))
            else [ GClockIwEffect(IwClockEffectUpdateDone({ p_sid : p_sid, flag : One }))
                 , IwClockCreateEnvSimLog(clock, IwLogRoundOk(p_sid))
                 , PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectUpdateOutput(IwPartiesOutputRoundOk) })) ]
        }
    }

    pure def IwClockCorrupt(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [GClockIwEffect(IwClockEffectUpdateCorrupted(p_sid))]
    }

    pure def IwClockTransition(which : IwClockAction, clock : IwClockState) : Effects_t[IwEffect] = {
        match which {
            | IwClockActionRdInput    => {
                match ReadNewInput(clock.itm) {
                    | Some(input_message) => {
                        (match (input_message) {
                            | IwClockInputReg(p_sid)   => IwClockRegister(clock, p_sid)
                            | IwClockInputRound(p_sid) => IwClockPartyRound(clock, p_sid)
                            | IwClockInputOk(p_sid)    => IwClockOk(clock, p_sid)
                        }).append(GClockIwEffect(IwClockEffectUpdateItm(ItmEffectPopInput)))
                    }
                    | None => []
                }
            }
            | IwClockActionRdIncoming => {
                match ReadNewIncoming(clock.itm) {
                    | Some(incoming_message) => {
                        (match incoming_message {
                            | IwClockIncomingRound          => IwClockSimulatorRound(clock)
                            | IwClockIncomingCorrupt(p_sid) => IwClockCorrupt(p_sid)
                        }).append(GClockIwEffect(IwClockEffectUpdateItm(ItmEffectPopIncoming)))
                    }
                    | None => []
                }
            }
        }
    }

    // -------------------------------

    // Environment and Simulator
    // ^^^^^^^^^^^^^^^^^^^^^^^^^

    type IwEnvSimLog = {
        index : int,
        log   : IwLog,
        reg   : Set[P_Sid_t],
        c     : Set[P_Sid_t],
        ok    : Set[P_Sid_t],
        round : Round_t
    }

    type IwEnvSimState = {
        logs : Set[IwEnvSimLog]
    }

    type IwEnvSimEffect = IwEnvSimEffectLog({ log : IwLog, reg : Set[P_Sid_t], c : Set[P_Sid_t], ok : Set[P_Sid_t], round : Round_t })

    type IwEnvSimAction = IwEnvSimActionSetOk(P_Sid_t)
                        | IwEnvSimActionGetRound(P_Sid_t)
                        | IwEnvSimActionRegister(P_Sid_t)

    pure def IwEnvSimNewLog(log : IwLog, index : int, reg : Set[P_Sid_t], c : Set[P_Sid_t], ok : Set[P_Sid_t], round : Round_t) : IwEnvSimLog =
        { index : index, log : log, reg : reg, c : c, ok : ok, round : round }

    pure def IwEnvSimLogPush(logs: Set[IwEnvSimLog], l: IwLog, reg : Set[P_Sid_t], c : Set[P_Sid_t], ok : Set[P_Sid_t], round : Round_t) : Set[IwEnvSimLog] =
        if (size(logs) >= LogsSize) {
            val kept = logs.filter(x => x.index > 0)
                           .map(x => { index: x.index - 1, log : x.log, reg : x.reg, c : x.c, ok : x.ok, round : x.round })
            kept.union(Set(IwEnvSimNewLog(l, size(kept), reg, c, ok, round)))
        } else {
            logs.union(Set(IwEnvSimNewLog(l, size(logs), reg, c, ok, round)))
        }

    pure def IwEnvSimApplyEffect(state : IwEnvSimState, effect : IwEnvSimEffect) : IwEnvSimState = {
        match effect {
            | IwEnvSimEffectLog(r) => state.with("logs", IwEnvSimLogPush(state.logs, r.log, r.reg, r.c, r.ok, r.round))
        }
    }

    pure def IwEnvSimInit : IwEnvSimState = { logs : Set() }

    pure def IwEnvSimRound(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid: p_sid, effect : ItmEffectUpdateInput(IwPartiesInputRound) }))]
    }

    pure def IwEnvSimOk(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [ PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid: p_sid, effect : ItmEffectUpdateInput(IwPartiesInputOk) })) ]
    }

    pure def IwEnvSimReg(p_sid : P_Sid_t, clock : IwClockState) : Effects_t[IwEffect] = {
         [ PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid: p_sid, effect : ItmEffectUpdateInput(IwPartiesInputReg) }))
         , IwClockCreateEnvSimLog(clock, IwLogReg(p_sid))]
    }

    pure def IwEnvSimAllRegistered(zs : IwEnvSimState) : bool = {
        size((zs.logs.fold(Set(), (acc, l) => match l.log {
            | IwLogRegOk(p_sid) => acc.union(Set(p_sid))
            | _                 => acc
        }))) >= NumberOfParties
    }

    pure def IwEnvSimRegistered(zs : IwEnvSimState, p_sid : P_Sid_t) : bool = {
        zs.logs.fold(false, (acc, l) => match l.log {
            | IwLogRegOk(p) => acc or (p == p_sid)
            | _ => acc
        })
    }

    pure def IwEnvSimTransition(which : IwEnvSimAction, zs : IwEnvSimState, idle : bool, clock : IwClockState) : Effects_t[IwEffect] = {
        if (not(idle)) []
        else match which {
            | IwEnvSimActionRegister(p_sid) => if (IwEnvSimRegistered(zs, p_sid)) [] else IwEnvSimReg(p_sid, clock)
            | IwEnvSimActionSetOk(p_sid)    => if (IwEnvSimAllRegistered(zs)) IwEnvSimOk(p_sid) else []
            | IwEnvSimActionGetRound(p_sid) => if (IwEnvSimAllRegistered(zs)) IwEnvSimRound(p_sid) else []
        }
    }

    // -----------------------------------------------------------------

    // Dummy Parties
    // ^^^^^^^^^^^^^

    type IwPartiesInput = IwPartiesInputReg   // in the paper Psid.Reg()
                        | IwPartiesInputRound // in the paper Psid.Round()
                        | IwPartiesInputOk    // in the paper Psid.OK()

    type IwPartiesOutput = IwPartiesOutputRound(Round_t) // in the paper Psid.Round()
                         | IwPartiesOutputRegisterOk      // in the paper ok
                         | IwPartiesOutputRoundOk         // in the paper ok
                         | IwPartiesOutputFailed          // in the paper ⊥

    type IwPartiesIncoming = ()

    type IwPartyITM = ITM[IwPartiesInput, IwPartiesOutput, IwPartiesIncoming]

    type IwPartyState = {
        itm : IwPartyITM,
    }

    type IwPartiesState = P_Sid_t -> IwPartyState

    pure def Iw_get_p_sid(p : IwPartyState) : P_Sid_t = {
        match (p.itm.sid) {
            | P_Sid(p_sid) => p_sid
            | _            => InvalidP_Sid
        }
    }

    type IwPartiesAction = IwPartiesActionRdInput | IwPartiesActionRdOutput

    type IwPartiesEffect = IwPartiesEffectUpdateItm({p_sid : P_Sid_t, effect : ItmEffect[IwPartiesInput, IwPartiesOutput, IwPartiesIncoming]})

    pure def IwPartiesApplyEffect(state : IwPartiesState, effect : IwPartiesEffect) : IwPartiesState = {
        match (effect) {
            | IwPartiesEffectUpdateItm(r) => state.put(r.p_sid, state.get(r.p_sid).with("itm", ItmApplyEffect(state.get(r.p_sid).itm, r.effect)))
        }
    }

    // Action called by Z.
    // It initializes P's state.
    pure def IwPartiesInit : IwPartiesState = 1.to(NumberOfParties).mapBy(i => ({ itm : ItmInit(P_Sid(i)) }))

    // Action called by the party when receiving Reg from Z on
    // the input-tape.
    // Finally it puts an Reg message in the G-Clock's input-tape.
    pure def IwPartiesRegister(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [GClockIwEffect(IwClockEffectUpdateItm(ItmEffectUpdateInput(IwClockInputReg(p_sid))))]
    }

    pure def IwPartiesRound(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [GClockIwEffect(IwClockEffectUpdateItm(ItmEffectUpdateInput(IwClockInputRound(p_sid))))]
    }

    pure def IwPartiesRoundToZ(p_sid : P_Sid_t, round : Round_t, clock : IwClockState) : Effects_t[IwEffect] = {
        [IwClockCreateEnvSimLog(clock, IwLogPRound({ p_sid : p_sid, round : round }))]
    }

    pure def IwPartiesOk(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [GClockIwEffect(IwClockEffectUpdateItm(ItmEffectUpdateInput(IwClockInputOk(p_sid))))]
    }

    pure def IwPartiesMaybeOkToZ(p_sid : P_Sid_t, response : IwPartiesOutput, clock : IwClockState) : Effects_t[IwEffect] = {
        [IwClockCreateEnvSimLog(clock, match response {
                                                        | IwPartiesOutputRoundOk    => IwLogRoundOk(p_sid)
                                                        | IwPartiesOutputRegisterOk => IwLogRegOk(p_sid)
                                                        | IwPartiesOutputFailed     => IwLogFailed(p_sid)
                                                        | _                         => IwLogFailed(p_sid)})]
    }

    pure def IwPartiesTransition(which : IwPartiesAction, p_sid : P_Sid_t, parties : IwPartiesState, clock : IwClockState) : Effects_t[IwEffect] = {
        match which {
            | IwPartiesActionRdInput    => {
                match ReadNewInput(parties.get(p_sid).itm) {
                    | Some(input_message) => {
                        (match (input_message) {
                            | IwPartiesInputReg   => IwPartiesRegister(p_sid)
                            | IwPartiesInputRound => IwPartiesRound(p_sid)
                            | IwPartiesInputOk    => IwPartiesOk(p_sid)
                        }).append(PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectPopInput })))
                    }
                    | None => []
                }
            }
            | IwPartiesActionRdOutput => {
                match ReadNewOutput(parties.get(p_sid).itm) {
                    | Some(output_message) => {
                        (match output_message {
                            | IwPartiesOutputRound(r)   => IwPartiesRoundToZ(p_sid, r, clock)
                            | IwPartiesOutputFailed     => IwPartiesMaybeOkToZ(p_sid, IwPartiesOutputFailed, clock)
                            | IwPartiesOutputRegisterOk => IwPartiesMaybeOkToZ(p_sid, IwPartiesOutputRegisterOk, clock)
                            | IwPartiesOutputRoundOk    => IwPartiesMaybeOkToZ(p_sid, IwPartiesOutputRoundOk, clock)
                        }).append(PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectPopOutput })))
                    }
                    | None => []
                }
            }
        }
    }

    // -----------------------------------------------------------------

    // Main
    // ^^^^

    action IwInit = all {
        Iw_ZS'        = IwEnvSimInit,
        Iw_GClock'   = IwClockInit,
        Iw_Parties'  = IwPartiesInit,
        Iw_overflow' = false
    }

    action IwStep = {
        val idle   = IwStayIdle(Iw_GClock, Iw_Parties)
        nondet who = oneOf(Set(ZS_Sid, GClock_Sid, P_Sid(InvalidP_Sid)))

        match who {
            | ZS_Sid => {
                // Environment and Simulator
                nondet p_sid_z = oneOf(1.to(NumberOfParties))
                nondet which_z = oneOf(Set( IwEnvSimActionRegister(p_sid_z)
                                          , IwEnvSimActionSetOk(p_sid_z)
                                          , IwEnvSimActionGetRound(p_sid_z)))

                IwUpdate(IwEnvSimTransition(which_z, Iw_ZS, idle, Iw_GClock))
            }

            | P_Sid(_) => {
                // Parties
                nondet which_p = oneOf(Set( IwPartiesActionRdOutput
                                          , IwPartiesActionRdInput ))
                nondet p_sid_p = oneOf(1.to(NumberOfParties))

                IwUpdate(IwPartiesTransition(which_p, p_sid_p, Iw_Parties, Iw_GClock))
            }

            | GClock_Sid => {
                // GClock
                nondet which_g = oneOf(Set( IwClockActionRdInput
                                          , IwClockActionRdIncoming ))

                IwUpdate(IwClockTransition(which_g, Iw_GClock))
            }
        }
    }

    action IwUpdate(effects : Effects_t[IwEffect]) : bool = {
        val w = effects.foldl( { zs : Iw_ZS, g : Iw_GClock, p : Iw_Parties }
                             , (acc, e) => IwApplyEffect(acc, e))

        if (IwWorldFits(w)) all {
            Iw_ZS'        = w.zs,
            Iw_GClock'   = w.g,
            Iw_Parties'  = w.p,
            Iw_overflow' = Iw_overflow
        } else all {
            Iw_ZS'        = Iw_ZS,
            Iw_GClock'   = Iw_GClock,
            Iw_Parties'  = Iw_Parties,
            Iw_overflow' = true
        }
    }

    // -----------------------------------------------------------------

    // Properties
    // ^^^^^^^^^^

    // MUST FAIL
    // ^^^^^^^^^

    val RoundPastBound =
        Iw_GClock.current_round < MaxRound

    // MUST PASS
    // ^^^^^^^^^

    // For correctness
    val NoOverflow =
        not(Iw_overflow)

    val RoundBounded =
        Iw_GClock.current_round <= MaxRound

    // Property 1 (Time Agreement): If two parties query the time and no OK requests have been sent
    // in the middle then G-clock responds with the same time.
    val TimeAgreement =
       Iw_ZS.logs.forall(l1 =>
            match l1.log {
                | IwLogPRound(r1) => {
                    Iw_ZS.logs.forall(l2 =>
                        match l2.log {
                            | IwLogPRound(r2) =>
                                (l2.index > l1.index) implies {
                                    val no_ok_between = Iw_ZS.logs.forall(lm =>
                                        and { lm.index > l1.index, lm.index < l2.index } implies {
                                            match lm.log {
                                                | IwLogRoundOk(_) => false
                                                | _               => true
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

    // Property 2 (Time Liveness):  If all registered honest parties are ready, then time advances.
    // this is non-trivial since we have to track who was registered and corrupted at all times
    val TimeLiveness =
        Iw_ZS.logs.forall(l2 =>
            Iw_ZS.logs.forall(l1 =>
                (l1.index + 1 == l2.index) implies
                match l2.log {
                    | IwLogRoundOk(p) => {
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
    val TimeSoundness =
        Iw_ZS.logs.forall(l2 =>
            Iw_ZS.logs.forall(l1 =>
                and { l1.index + 1 == l2.index, l2.round > l1.round } implies
                match l2.log {
                    | IwLogRoundOk(p) => {
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
}

// -----------------------------------------------------------------

// Real-world Model
// ^^^^^^^^^^^^^^^^

module rw {
    import uc.*
    import utils.*

    // -----------------------------------------------------------------

    // Globals
    // ^^^^^^^

    var Rw_Z        : ()
    var Rw_A        : ()
    var Rw_FBD      : ()
    var Rw_Parties  : ()

    var Rw_overflow : bool
}

// Main
// ^^^^

module uc_gclock {
    import iw.*

    action init = all {
        IwInit
    }

    action step = all {
        IwStep
    }
}
