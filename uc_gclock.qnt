// Model Checking G-Clock
// from: https://eprint.iacr.org/2026/292.pdf

// -----------------------------------------------------------------

// Utils
// ^^^^^

module assumptions {
    pure val NumberOfParties = 2

    pure val CorruptedBound  = 1

    pure val MaxRound        = 10

    pure val TapeSize        = 1
}

module utils {
    type Round_t = int

    pure def FirstRound : int = 0

    // ^^^^^

    type P_Sid_t = int

    type Sid_t = S_Sid | Z_Sid | P_Sid(P_Sid_t) | GClock_Sid

    pure def InvalidP_Sid : int = -1

    // ^^^^^

    type Flag_t = bool

    pure def One : Flag_t = true

    pure def Zero : Flag_t = false

    // ^^^^^

    type Option_t[a] = Some(a) | None

    // ^^^^^

    type Effects_t[a] = List[a]
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

    var Iw_Z        : IwEnvironmentState
    var Iw_S        : IwSimulatorState
    var Iw_GClock   : IwClockState
    var Iw_Parties  : IwPartiesState

    var Iw_prev_Z        : Option_t[IwEnvironmentState]
    var Iw_prev_S        : Option_t[IwSimulatorState]
    var Iw_prev_GClock   : Option_t[IwClockState]
    var Iw_prev_Parties  : Option_t[IwPartiesState]

    // Set when a step needed more than TapeSize slots on some tape.
    var Iw_overflow : bool

    // -----------------------------------------------------------------

    // Effect
    // ^^^^^^^

    type IwEffect = GClockIwEffect(IwClockEffect)
                  | EnvironmentIwEffect(IwEnvironmentEffect)
                  | SimulatorIwEffect(IwSimulatorEffect)
                  | PartiesIwEffect(IwPartiesEffect)

    type IwWorld = {
        z : IwEnvironmentState,
        s : IwSimulatorState,
        g : IwClockState,
        p : IwPartiesState,
    }

    pure def IwApplyEffect(w : IwWorld, e : IwEffect) : IwWorld = {
        match e {
            | EnvironmentIwEffect(x) => w.with("z", IwEnvironmentApplyEffect(w.z, x))
            | SimulatorIwEffect(x)   => w.with("s", IwSimulatorApplyEffect(w.s, x))
            | GClockIwEffect(x)      => w.with("g", IwClockApplyEffect(w.g, x))
            | PartiesIwEffect(x)     => w.with("p", IwPartiesApplyEffect(w.p, x))
        }
    }

    pure def IwWorldFits(w : IwWorld) : bool = {
        and {
            ItmFits(w.s.itm),
            ItmFits(w.g.itm),
            w.p.keys().forall(k => ItmFits(w.p.get(k).itm)),
        }
    }

    pure def IwStayIdle(s : IwSimulatorState, g : IwClockState, p : IwPartiesState) : bool = {
        and {
            ItmIsEmpty(s.itm),
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

    pure def IwClockInit : IwClockState = {
        itm                : ItmInit(GClock_Sid),
        current_round      : FirstRound,
        registered_parties : Set(),
        corrupted_parties  : Set(),
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
        [SimulatorIwEffect(IwSimulatorEffectUpdateItm(ItmEffectUpdateIncoming(IwSimulatorIncomingRound(clock.current_round))))]
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
            else [ GClockIwEffect(IwClockEffectUpdateDone({ p_sid : p_sid, flag : One }))
                 , SimulatorIwEffect(IwSimulatorEffectUpdateItm(ItmEffectUpdateIncoming(IwSimulatorIncomingOk(p_sid))))
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

    // -----------------------------------------------------------------

    // Simulator
    // ^^^^^^^^^

    type IwSimulatorInput = IwSimulatorInputCorrupt(P_Sid_t)

    type IwSimulatorOutput = ()

    type IwSimulatorIncoming = IwSimulatorIncomingRound(Round_t)
                             | IwSimulatorIncomingOk(P_Sid_t)


    type IwSimulatorITM = ITM[IwSimulatorInput, IwSimulatorOutput, IwSimulatorIncoming]

    type IwSimulatorState = {
        itm               : IwSimulatorITM,
        parties_that_oked : Set[P_Sid_t],
        corrupted_parties : Set[P_Sid_t],
        current_round     : Round_t
    }

    type IwSimulatorAction = IwSimulatorActionRoundRequest
                           | IwSimulatorActionRdIncoming
                           | IwSimulatorActionRdInput

    type IwSimulatorEffect = IwSimulatorEffectUpdateItm(ItmEffect[IwSimulatorInput, IwSimulatorOutput, IwSimulatorIncoming])
                         | IwSimulatorEffectUpdatedOked(P_Sid_t)
                         | IwSimulatorEffectUpdateCorrupted(P_Sid_t)
                         | IwSimulatorEffectUpdateRound(Round_t)

    pure def IwSimulatorApplyEffect(state : IwSimulatorState, effect : IwSimulatorEffect) : IwSimulatorState = {
        match effect {
            | IwSimulatorEffectUpdateItm(e)           => state.with("itm", ItmApplyEffect(state.itm, e))
            | IwSimulatorEffectUpdatedOked(p_sid)     => state.with("parties_that_oked", state.parties_that_oked.union(Set(p_sid)))
            | IwSimulatorEffectUpdateCorrupted(p_sid) => state.with("corrupted_parties", state.corrupted_parties.union(Set(p_sid)))
            | IwSimulatorEffectUpdateRound(round)     => state.with("current_round", round)
        }
    }

    pure def IwSimulatorInit : IwSimulatorState = {
        itm               : ItmInit(S_Sid),
        parties_that_oked : Set(),
        corrupted_parties : Set(),
        current_round     : FirstRound
    }

    pure def IwSimulatorRound : Effects_t[IwEffect] = {
        [GClockIwEffect(IwClockEffectUpdateItm(ItmEffectUpdateIncoming(IwClockIncomingRound)))]
    }

    pure def IwSimulatorRoundResponse(round : Round_t) : Effects_t[IwEffect] = {
        [SimulatorIwEffect(IwSimulatorEffectUpdateRound(round))]
    }

    pure def IwSimulatorCorrupt(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [ GClockIwEffect(IwClockEffectUpdateItm(ItmEffectUpdateIncoming(IwClockIncomingCorrupt(p_sid))))
        , SimulatorIwEffect(IwSimulatorEffectUpdateCorrupted(p_sid)) ]
    }

    pure def IwSimulatorOked(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [SimulatorIwEffect(IwSimulatorEffectUpdatedOked(p_sid))]
    }

    pure def IwSimulatorNumberOfCorrupted(s : IwSimulatorState) : int = {
        size(s.corrupted_parties)
    }

    pure def IwSimulatorTransition(which : IwSimulatorAction, s : IwSimulatorState, idle : bool) : Effects_t[IwEffect] = {
        match which {
            | IwSimulatorActionRdInput        => match ReadNewInput(s.itm) {
                                                    | Some(input_message) => {
                                                        (match input_message {
                                                            | IwSimulatorInputCorrupt(p_sid) => IwSimulatorCorrupt(p_sid)
                                                        }).append(SimulatorIwEffect(IwSimulatorEffectUpdateItm(ItmEffectPopInput)))
                                                    }
                                                    | _ => []
                                                 }
            | IwSimulatorActionRoundRequest   => if (idle) IwSimulatorRound else []
            | IwSimulatorActionRdIncoming     => match ReadNewIncoming(s.itm) {
                                                    | Some(incoming_message) => {
                                                        (match incoming_message {
                                                            | IwSimulatorIncomingRound(round) => IwSimulatorRoundResponse(round)
                                                            | IwSimulatorIncomingOk(p_sid)    => IwSimulatorOked(p_sid)
                                                        }).append(SimulatorIwEffect(IwSimulatorEffectUpdateItm(ItmEffectPopIncoming)))
                                                    }
                                                    | None => []
                                               }
        }
    }

    // -----------------------------------------------------------------

    // Environment
    // ^^^^^^^^^^^

    type IwEnvironmentOutput = IwEnvironmentOutputCorrupted(P_Sid_t)
                             | IwEnvironmentOutputRegisterOk(P_Sid_t)                         // in the paper ok
                             | IwEnvironmentOutputRoundOk(P_Sid_t)                            // in the paper ok
                             | IwEnvironmentOutputRound({ p_sid : P_Sid_t, round : Round_t }) // in the paper r
                             | IwEnvironmentOutputFailed(P_Sid_t)                             // in the paper ⊥

    type IwEnvironmentState = {
        registered : Set[P_Sid_t],
        seen_round : P_Sid_t -> Round_t,
        corrupted  : Set[P_Sid_t]
    }

    type IwEnvironmentEffect = IwEnvironmentEffectObserve(IwEnvironmentOutput)
                             | IwEnvironmentEffectClearRounds
                             | IwEnvironmentEffectUpdateRegistered(P_Sid_t)
                             | IwEnvironmentEffectUpdateCorrupted(P_Sid_t)

    type IwEnvironmentAction = IwEnvironmentActionSetOk(P_Sid_t)
                             | IwEnvironmentActionGetRound(P_Sid_t)
                             | IwEnvironmentActionRegister(P_Sid_t)
                             | IwEnvironmentActionCorrupt(P_Sid_t)

    pure def IwEnvironmentApplyEffect(state : IwEnvironmentState, effect : IwEnvironmentEffect) : IwEnvironmentState = {
        match (effect) {
            | IwEnvironmentEffectObserve(out) =>
                match out {
                    | IwEnvironmentOutputRegisterOk(p) => state.with("registered", state.registered.union(Set(p)))
                    | IwEnvironmentOutputRound(r)      => state.with("seen_round", state.seen_round.put(r.p_sid, r.round))
                    | _                                => state
                }
            | IwEnvironmentEffectClearRounds             => state.with("seen_round", Map())
            | IwEnvironmentEffectUpdateCorrupted(p_sid)  => state.with("corrupted", state.corrupted.union(Set(p_sid)))
            | IwEnvironmentEffectUpdateRegistered(p_sid) => state.with("registered", state.registered.union(Set(p_sid)))
        }
    }

    pure def IwEnvironmentInit : IwEnvironmentState = { registered : Set(), seen_round : Map(), corrupted : Set() }

    pure def IwEnvironmentRound(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid: p_sid, effect : ItmEffectUpdateInput(IwPartiesInputRound) }))]
    }

    pure def IwEnvironmentOk(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [ PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid: p_sid, effect : ItmEffectUpdateInput(IwPartiesInputOk) }))
        , EnvironmentIwEffect(IwEnvironmentEffectClearRounds) ]
    }

    pure def IwEnvironmentCorrupt(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [ SimulatorIwEffect(IwSimulatorEffectUpdateItm(ItmEffectUpdateInput(IwSimulatorInputCorrupt(p_sid))))
        , EnvironmentIwEffect(IwEnvironmentEffectUpdateCorrupted(p_sid))]
    }

    pure def IwEnvironmentReg(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
         [ PartiesIwEffect(IwPartiesEffectUpdateItm({ p_sid: p_sid, effect : ItmEffectUpdateInput(IwPartiesInputReg) }))
         , EnvironmentIwEffect(IwEnvironmentEffectUpdateRegistered(p_sid))]
    }

    pure def IwEnvironmentAllRegistered(z : IwEnvironmentState) : bool = {
        size(z.registered) >= NumberOfParties
    }

    pure def IwEnvironmentTransition(which : IwEnvironmentAction, z : IwEnvironmentState, idle : bool) : Effects_t[IwEffect] = {
        if (not(idle)) []
        else match which {
            | IwEnvironmentActionRegister(p_sid) => if (z.registered.contains(p_sid)) [] else IwEnvironmentReg(p_sid)
            | IwEnvironmentActionSetOk(p_sid)    => if (IwEnvironmentAllRegistered(z)) IwEnvironmentOk(p_sid) else []
            | IwEnvironmentActionGetRound(p_sid) => if (IwEnvironmentAllRegistered(z)) IwEnvironmentRound(p_sid) else []
            | IwEnvironmentActionCorrupt(p_sid)  => if (z.registered.contains(p_sid) and size(z.corrupted) < CorruptedBound) IwEnvironmentCorrupt(p_sid) else []
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

    pure def IwPartiesRoundToZ(p_sid : P_Sid_t, round : Round_t) : Effects_t[IwEffect] = {
        [EnvironmentIwEffect(IwEnvironmentEffectObserve(IwEnvironmentOutputRound({ p_sid : p_sid, round : round })))]
    }

    pure def IwPartiesOk(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [GClockIwEffect(IwClockEffectUpdateItm(ItmEffectUpdateInput(IwClockInputOk(p_sid))))]
    }

    pure def IwPartiesMaybeOkToZ(p_sid : P_Sid_t, response : IwPartiesOutput) : Effects_t[IwEffect] = {
        [EnvironmentIwEffect(IwEnvironmentEffectObserve(match response {
                                                        | IwPartiesOutputRoundOk    => IwEnvironmentOutputRoundOk(p_sid)
                                                        | IwPartiesOutputRegisterOk => IwEnvironmentOutputRegisterOk(p_sid)
                                                        | IwPartiesOutputFailed     => IwEnvironmentOutputFailed(p_sid)
                                                        | _                         => IwEnvironmentOutputFailed(p_sid)}))]
    }

    pure def IwPartiesTransition(which : IwPartiesAction, p_sid : P_Sid_t, parties : IwPartiesState) : Effects_t[IwEffect] = {
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
                            | IwPartiesOutputRound(r)   => IwPartiesRoundToZ(p_sid, r)
                            | IwPartiesOutputFailed     => IwPartiesMaybeOkToZ(p_sid, IwPartiesOutputFailed)
                            | IwPartiesOutputRegisterOk => IwPartiesMaybeOkToZ(p_sid, IwPartiesOutputRegisterOk)
                            | IwPartiesOutputRoundOk    => IwPartiesMaybeOkToZ(p_sid, IwPartiesOutputRoundOk)
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
        Iw_Z'        = IwEnvironmentInit,
        Iw_S'        = IwSimulatorInit,
        Iw_GClock'   = IwClockInit,
        Iw_Parties'  = IwPartiesInit,
        Iw_overflow' = false,

        // for time soundness property
        Iw_prev_Z'       = None,
        Iw_prev_S'       = None,
        Iw_prev_GClock'  = None,
        Iw_prev_Parties' = None
    }

    action IwStep = all {
        val idle = IwStayIdle(Iw_S, Iw_GClock, Iw_Parties)
        nondet who = oneOf(Set(Z_Sid, S_Sid, GClock_Sid, P_Sid(InvalidP_Sid)))

        match who {
            | Z_Sid => {
                // Environment
                nondet p_sid_z = oneOf(1.to(NumberOfParties))
                nondet which_z = oneOf(Set( IwEnvironmentActionRegister(p_sid_z)
                                          , IwEnvironmentActionSetOk(p_sid_z)
                                          , IwEnvironmentActionGetRound(p_sid_z)
                                          , IwEnvironmentActionCorrupt(p_sid_z)))

                IwUpdate(IwEnvironmentTransition(which_z, Iw_Z, idle))
            }

            | P_Sid(_) => {
                // Parties
                nondet which_p = oneOf(Set( IwPartiesActionRdOutput
                                          , IwPartiesActionRdInput ))
                nondet p_sid_p = oneOf(1.to(NumberOfParties))

                IwUpdate(IwPartiesTransition(which_p, p_sid_p, Iw_Parties))
            }

            | S_Sid => {
                // Simulator
                nondet which_s = oneOf(Set( IwSimulatorActionRoundRequest
                                          , IwSimulatorActionRdIncoming
                                          , IwSimulatorActionRdInput))

                IwUpdate(IwSimulatorTransition(which_s, Iw_S, idle))
            }

            | GClock_Sid => {
                // GClock
                nondet which_g = oneOf(Set( IwClockActionRdInput
                                          , IwClockActionRdIncoming ))

                IwUpdate(IwClockTransition(which_g, Iw_GClock))
            }
        },

        // for time soundness property
        Iw_prev_Z'       = Some(Iw_Z),
        Iw_prev_S'       = Some(Iw_S),
        Iw_prev_GClock'  = Some(Iw_GClock),
        Iw_prev_Parties' = Some(Iw_Parties)
    }

    action IwUpdate(effects : Effects_t[IwEffect]) : bool = {
        val w = effects.foldl({ z : Iw_Z, s : Iw_S, g : Iw_GClock, p : Iw_Parties }, (acc, e) => IwApplyEffect(acc, e))

        if (IwWorldFits(w)) all {
            Iw_Z'        = w.z,
            Iw_S'        = w.s,
            Iw_GClock'   = w.g,
            Iw_Parties'  = w.p,
            Iw_overflow' = Iw_overflow
        } else all {
            Iw_Z'        = Iw_Z,
            Iw_S'        = Iw_S,
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

    val SeenRounds =
        size(Iw_Z.seen_round.keys()) < MaxRound

    // MUST PASS
    // ^^^^^^^^^

    // For correctness
    val NoOverflow    =
        not(Iw_overflow)

    val RoundBounded  =
        Iw_GClock.current_round <= MaxRound

    // Property 1: Time Agreement: If two parties query the time and no OK requests have been sent
    // in the middle then G-clock responds with the same time.
    val TimeAgreement =
        Iw_Z.seen_round.keys().forall(p1 =>
            Iw_Z.seen_round.keys().forall(p2 =>
                Iw_Z.seen_round.get(p1) == Iw_Z.seen_round.get(p2)
            )
        )

    // Property 2 (Time Liveness):  If all registered parties are ready, then time advances.
    // this is non-trivial since we have to track who was registered and corrupted at all times
    val TimeLiveness =
        match Iw_prev_GClock {
            | Some(pc) =>
                match ReadNewInput(pc.itm) {
                    | Some(i) =>
                        match i {
                            | IwClockInputOk(p) =>
                                and {
                                    // to make sure it checks cases where the message was consumed after
                                    length(pc.itm.input) == 1,
                                    length(Iw_GClock.itm.input) == 0,

                                    // because at the max round it saturates
                                    pc.current_round < MaxRound,

                                    pc.registered_parties.contains(p),
                                    pc.registered_parties
                                        .exclude(pc.corrupted_parties)
                                        .forall(q =>
                                            q == p or pc.done.get(q) == One
                                        )
                                }.implies(
                               Iw_GClock.current_round == pc.current_round + 1
                                )
                            | _ => true
                        }
                    | _ => true
                }
            | None => true
        }

    // Property 3: TimeLiveness: If time advanced then all currently registered honest parties were ready.
    val TimeSoundness =
        match Iw_prev_GClock {
            | Some(pc) =>
                (pc.current_round < Iw_GClock.current_round).implies(
                    match ReadNewInput(pc.itm) {
                        | Some(i) =>
                            match i {
                                | IwClockInputOk(p) => and {
                                    pc.registered_parties.contains(p),
                                    pc.registered_parties.exclude(pc.corrupted_parties)
                                        .forall(q => q == p or pc.done.get(q) == One),
                                }
                                | _ => false
                            }

                        | _ => false
                    })
            | None => true
        }
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

    // Set when a step needed more than TapeSize slots on some tape.
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
