// Model Checking G-Clock and G-Slot against the Relative Time protocol
// from: https://eprint.iacr.org/2026/292.pdf

// -----------------------------------------------------------------

// Real-world Model
// ^^^^^^^^^^^^^^^^

module rw {
    import uc.* from "./uc"
    import utils.* from "./utils"
    import assumptions.* from "./assumptions"
    import logs.* from "./logs"
    import time.* from "./time"

    type Rw_Sid_t = Rw_ZS_Sid
                  | Rw_P_Sid(P_Sid_t)
                  | Rw_FLocal_Sid(P_Sid_t)
                  | Rw_FDDiffuse_Sid(P_Sid_t)
                  | Rw_GrefRate_Sid

    type RwItm[in, out, incoming] = ITM[Rw_Sid_t, in, out, incoming]

    // -----------------------------------------------------------------

    // Globals
    // ^^^^^^^

    var Rw_ZS         : RwEnvSimState
    var Rw_GrefRate   : RwGrefRateState
    var Rw_FLocals    : RwFLocalsState
    var Rw_FDDiffuses : RwFDDiffusesState
    var Rw_Parties    : RwPartiesState

    // Set when a step needed more than TapeSize / InboxSize slots.
    var Rw_overflow   : bool

    pure val RwMaxTime  = MaxRound * RoundDuration
    pure val RwMaxClock = RwMaxTime + MaxDrift

    // -----------------------------------------------------------------

    // Effect
    // ^^^^^^

    type RwEffect = GrefRateRwEffect(RwGrefRateEffect)
                  | FLocalsRwEffect(RwFLocalsEffect)
                  | FDDiffusesRwEffect(RwFDDiffusesEffect)
                  | PartiesRwEffect(RwPartiesEffect)
                  | EnvSimRwEffect(RwEnvSimEffect)

    type RwWorld = {
        zs : RwEnvSimState,
        g  : RwGrefRateState,
        l  : RwFLocalsState,
        d  : RwFDDiffusesState,
        p  : RwPartiesState,
    }

    pure def RwApplyEffect(w : RwWorld, e : RwEffect) : RwWorld = {
        match e {
            | EnvSimRwEffect(x)    => w.with("zs", RwEnvSimApplyEffect(w.zs, x))
            | GrefRateRwEffect(x)  => w.with("g", RwGrefRateApplyEffect(w.g, x))
            | FLocalsRwEffect(x)   => w.with("l", RwFLocalsApplyEffect(w.l, x))
            | FDDiffusesRwEffect(x) => w.with("d", RwFDDiffusesApplyEffect(w.d, x))
            | PartiesRwEffect(x)   => w.with("p", RwPartiesApplyEffect(w.p, x))
        }
    }

    pure def RwWorldFits(w : RwWorld) : bool = {
        and {
            ItmFits(w.g.itm),
            w.l.keys().forall(k => ItmFits(w.l.get(k).itm)),
            w.d.keys().forall(k => and {
                ItmFits(w.d.get(k).itm),
                length(w.d.get(k).inbox) <= InboxSize,
            }),
            w.p.keys().forall(k => ItmFits(w.p.get(k).itm)),
        }
    }

    pure def RwStayIdle(w : RwWorld) : bool = {
        and {
            ItmIsEmpty(w.g.itm),
            w.l.keys().forall(k => ItmIsEmpty(w.l.get(k).itm)),
            w.d.keys().forall(k => ItmIsEmpty(w.d.get(k).itm)),
            w.p.keys().forall(k => ItmIsEmpty(w.p.get(k).itm)),
        }
    }

    // Shortcuts: put a message on a tape of some ITM.
    pure def RwToParty(p_sid : P_Sid_t, e : ItmEffect[RwPartyInput, RwPartyOutput, RwPartyIncoming]) : RwEffect =
        PartiesRwEffect(RwPartiesEffectsUpdateItm({ p_sid : p_sid, effect : e }))

    pure def RwToFLocal(p_sid : P_Sid_t, e : ItmEffect[RwFLocalInput, RwFLocalOutput, RwFLocalIncoming]) : RwEffect =
        FLocalsRwEffect(RwFLocalsEffectUpdateItm({ p_sid : p_sid, effect : e }))

    pure def RwToFDDiffuse(p_sid : P_Sid_t, e : ItmEffect[RwFDDiffuseInput, RwFDDiffuseOutput, RwFDDiffuseIncoming]) : RwEffect =
        FDDiffusesRwEffect(RwFDDiffuseEffectUpdateItm({ p_sid : p_sid, effect : e }))

    pure def RwToGrefRate(e : ItmEffect[RwGrefRateInput, RwGrefRateOutput, RwGrefRateIncoming]) : RwEffect =
        GrefRateRwEffect(RwGrefRateEffectUpdateItm(e))

    // -----------------------------------------------------------------

    // Hybrid Functionalities
    // ^^^^^^^^^^^^^^^^^^^^^^

    // A block only carries the slot number its producer claims (all that the
    // relative time protocol looks at).
    type RwBlock = { slot : Round_t }

    // -----------------------------------------------------------------

    // G_refRate
    // ^^^^^^^^^

    type RwGrefRateInput = RwGrefRateInputRegister(Rw_Sid_t)
                         | RwGrefRateInputContinue

    type RwGrefRateOutput = ()

    type RwGrefRateIncoming = ()

    type RwGrefRateState = {
        registered : Set[Rw_Sid_t],
        itm        : RwItm[RwGrefRateInput, RwGrefRateOutput, RwGrefRateIncoming],
        counter    : Time_t,
        ok         : Set[P_Sid_t]
    }

    type RwGrefRateAction = | RwGrefRateActionRdInput

    type RwGrefRateEffect = RwGrefRateEffectRegister(Rw_Sid_t)
                          | RwGrefRateEffectIncrement
                          | RwGrefRateEffectAddOk(P_Sid_t)
                          | RwGrefRateEffectUpdateItm(ItmEffect[RwGrefRateInput, RwGrefRateOutput, RwGrefRateIncoming])

    pure def RwGrefRateApplyEffect(state : RwGrefRateState, effect : RwGrefRateEffect) : RwGrefRateState = {
        match (effect) {
            | RwGrefRateEffectRegister(sid) => state.with("registered", state.registered.union(Set(sid)))
            | RwGrefRateEffectIncrement     => {
                val c = min(state.counter + 1, RwMaxTime)
                state.with("counter", c).with("ok", if (c / RoundDuration != state.counter / RoundDuration) Set() else state.ok)
            }
            | RwGrefRateEffectAddOk(p_sid)  => state.with("ok", state.ok.union(Set(p_sid)))
            | RwGrefRateEffectUpdateItm(e)  => state.with("itm", ItmApplyEffect(state.itm, e))
        }
    }

    pure def RwGrefRateInit() : RwGrefRateState = {
        registered : Set(),
        itm : ItmInit(Rw_GrefRate_Sid),
        counter : TimeInit,
        ok : Set()
    }

    pure def RwCurrentSlot(g : RwGrefRateState) : Round_t = g.counter / RoundDuration

    pure def RwGrefRateRegister(sid : Rw_Sid_t) : Effects_t[RwEffect] = {
        [GrefRateRwEffect(RwGrefRateEffectRegister(sid))].concat(
            match sid {
                | Rw_FLocal_Sid(p)    => [RwToFLocal(p, ItmEffectUpdateOutput(RwFLocalOutputRegistered))]
                | Rw_FDDiffuse_Sid(p) => [RwToFDDiffuse(p, ItmEffectUpdateOutput(RwFDDiffuseOutputRegistered))]
                | _                   => []
            })
    }

    pure def RwGrefRateContinue(g : RwGrefRateState) : Effects_t[RwEffect] = {
        g.registered.fold([], (acc, sid) =>
            match sid {
                | Rw_FLocal_Sid(p)    => acc.append(RwToFLocal(p, ItmEffectUpdateOutput(RwFLocalInputContinue)))
                | Rw_FDDiffuse_Sid(p) => acc.append(RwToFDDiffuse(p, ItmEffectUpdateOutput(RwFDDiffuseOutputContinue)))
                | _                   => acc
            }).append(GrefRateRwEffect(RwGrefRateEffectIncrement))
    }

    pure def RwGrefRateTransition(which : RwGrefRateAction, g : RwGrefRateState) : Effects_t[RwEffect] = {
        match which {
            | RwGrefRateActionRdInput => {
                match ReadNewInput(g.itm) {
                    | Some(input_message) => {
                        (match input_message {
                            | RwGrefRateInputRegister(sid) => RwGrefRateRegister(sid)
                            | RwGrefRateInputContinue      => RwGrefRateContinue(g)
                        }).append(RwToGrefRate(ItmEffectPopInput))
                    }
                    | None => []
                }
            }
        }
    }

    // -----------------------------------------------------------------

    // F_Local
    // ^^^^^^^

    type RwFLocalInput = RwFLocalInputZIncrease
                       | RwFLocalInputGetClock
                       | RwFLocalInputRegister

    type RwFLocalOutput = RwFLocalOutputRegistered
                        | RwFLocalInputContinue

    type RwFLocalIncoming = ()

    type RwFLocalState = {
        local_counter   : Time_t,
        local_counter_z : Time_t,
        itm             : RwItm[RwFLocalInput, RwFLocalOutput, RwFLocalIncoming],
        is_registered   : bool
    }

    type RwFLocalsState = P_Sid_t -> RwFLocalState

    type RwFLocalAction = RwFLocalActionRdInput | RwFLocalActionRdOutput

    type RwFLocalsEffect = RwFLocalsEffectZIncrease(P_Sid_t)
                         | RwFLocalsEffectIncrease(P_Sid_t)
                         | RwFLocalsEffectUpdateItm({ p_sid: P_Sid_t, effect : ItmEffect[RwFLocalInput, RwFLocalOutput, RwFLocalIncoming] })
                         | RwFLocalsEffectSetRegistered(P_Sid_t)

    pure def RwFLocalsApplyEffect(state : RwFLocalsState, effect : RwFLocalsEffect) : RwFLocalsState = {
        match (effect) {
            | RwFLocalsEffectZIncrease(p_sid)        => state.put(p_sid, state.get(p_sid).with("local_counter_z", min(state.get(p_sid).local_counter_z + 1, RwMaxClock)))
            | RwFLocalsEffectIncrease(p_sid)         => state.put(p_sid, state.get(p_sid).with("local_counter", min(state.get(p_sid).local_counter + 1, RwMaxClock)))
            | RwFLocalsEffectUpdateItm(r)            => state.put(r.p_sid, state.get(r.p_sid).with("itm", ItmApplyEffect(state.get(r.p_sid).itm, r.effect)))
            | RwFLocalsEffectSetRegistered(p_sid)    => state.put(p_sid, state.get(p_sid).with("is_registered", true))
        }
    }

    pure def RwFLocalsInit() : RwFLocalsState =
        1.to(NumberOfParties).mapBy(i => ({ local_counter : TimeInit
                                          , local_counter_z : TimeInit
                                          , itm : ItmInit(Rw_FLocal_Sid(i))
                                          , is_registered : false }))

    pure def RwFLocalRegister(p_sid : P_Sid_t) : Effects_t[RwEffect] = {
        [ FLocalsRwEffect(RwFLocalsEffectSetRegistered(p_sid))
        , RwToGrefRate(ItmEffectUpdateInput(RwGrefRateInputRegister(Rw_FLocal_Sid(p_sid)))) ]
    }

    pure def RwFLocalZIncrease(p_sid : P_Sid_t) : Effects_t[RwEffect] = {
        [FLocalsRwEffect(RwFLocalsEffectZIncrease(p_sid))]
    }

    pure def RwFLocalIncrease(p_sid : P_Sid_t) : Effects_t[RwEffect] = {
        [FLocalsRwEffect(RwFLocalsEffectIncrease(p_sid))]
    }

    pure def RwFLocalGetClock(p_sid : P_Sid_t, local : RwFLocalState) : Effects_t[RwEffect] = {
        [RwToParty(p_sid, ItmEffectUpdateIncoming(RwPartyIncomingClock(local.local_counter_z)))]
    }

    pure def RwFLocalTransition(which : RwFLocalAction, p_sid : P_Sid_t, locals : RwFLocalsState) : Effects_t[RwEffect] = {
        match which {
            | RwFLocalActionRdInput => {
                match ReadNewInput(locals.get(p_sid).itm) {
                    | Some(input_message) => {
                        (match input_message {
                            | RwFLocalInputZIncrease => RwFLocalZIncrease(p_sid)
                            | RwFLocalInputGetClock  => RwFLocalGetClock(p_sid, locals.get(p_sid))
                            | RwFLocalInputRegister  => RwFLocalRegister(p_sid)
                        }).append(RwToFLocal(p_sid, ItmEffectPopInput))
                    }
                    | None => []
                }
            }
            | RwFLocalActionRdOutput => {
                match ReadNewOutput(locals.get(p_sid).itm) {
                    | Some(output_message) => {
                        (match output_message {
                            | RwFLocalOutputRegistered => [RwToFDDiffuse(p_sid, ItmEffectUpdateInput(RwFDDiffuseInputRegister))]
                            | RwFLocalInputContinue    => RwFLocalIncrease(p_sid)
                        }).append(RwToFLocal(p_sid, ItmEffectPopOutput))
                    }
                    | None => []
                }
            }
        }
    }

    // -----------------------------------------------------------------

    // F_DDiffuse
    // ^^^^^^^^^^

    type RwFDDiffuseMessage = {
        sender        : P_Sid_t,
        message       : RwBlock,
        timestamp     : Time_t
    }

    type RwFDDiffuseInput = RwFDDiffuseInputDiffuse(RwFDDiffuseMessage)
                          | RwFDDiffuseInputRegister
                          | RwFDDiffuseInputRelease(int)

    type RwFDDiffuseOutput = | RwFDDiffuseOutputRegistered
                             | RwFDDiffuseOutputContinue

    type RwFDDiffuseIncoming = ()

    type RwFDDiffuseState = {
        clock : Time_t,
        inbox : List[RwFDDiffuseMessage],
        itm   : RwItm[RwFDDiffuseInput, RwFDDiffuseOutput, RwFDDiffuseIncoming],
        is_registered : bool
    }

    type RwFDDiffusesState = P_Sid_t -> RwFDDiffuseState

    type RwFDDiffuseAction = RwFDDiffuseActionRdInput | RwFDDiffuseActionRdOutput

    type RwFDDiffusesEffect = RwFDDiffusesEffectIncrement(P_Sid_t)
                            | RwFDDiffusesEffectAddInbox({ p_sid : P_Sid_t, message : RwFDDiffuseMessage })
                            | RwFDDiffusesEffectRemainingInbox({ p_sid : P_Sid_t, remaining : List[RwFDDiffuseMessage] })
                            | RwFDDiffusesEffectSetRegistered(P_Sid_t)
                            | RwFDDiffuseEffectUpdateItm({ p_sid : P_Sid_t, effect : ItmEffect[RwFDDiffuseInput, RwFDDiffuseOutput, RwFDDiffuseIncoming] })

    pure def RwFDDiffusesApplyEffect(state : RwFDDiffusesState, effect : RwFDDiffusesEffect) : RwFDDiffusesState = {
        match (effect) {
            | RwFDDiffusesEffectIncrement(p_sid)       => state.put(p_sid, state.get(p_sid).with("clock", min(state.get(p_sid).clock + 1, RwMaxClock)))
            | RwFDDiffusesEffectAddInbox(r)            => state.put(r.p_sid, state.get(r.p_sid).with("inbox", state.get(r.p_sid).inbox.append(r.message)))
            | RwFDDiffusesEffectRemainingInbox(r)      => state.put(r.p_sid, state.get(r.p_sid).with("inbox", r.remaining))
            | RwFDDiffusesEffectSetRegistered(p_sid)   => state.put(p_sid, state.get(p_sid).with("is_registered", true))
            | RwFDDiffuseEffectUpdateItm(r)            => state.put(r.p_sid, state.get(r.p_sid).with("itm", ItmApplyEffect(state.get(r.p_sid).itm, r.effect)))
        }
    }

    pure def RwFDDiffusesInit() : RwFDDiffusesState =
        1.to(NumberOfParties).mapBy(i => ({ clock         : TimeInit
                                          , inbox         : []
                                          , itm           : ItmInit(Rw_FDDiffuse_Sid(i))
                                          , is_registered : false }))

    pure def RwFDDiffuseExpired(d : RwFDDiffuseState, m : RwFDDiffuseMessage) : bool =
        d.clock >= m.timestamp + Delta * RoundDuration

    pure def RwFDDiffuseRegister(p_sid : P_Sid_t) : Effects_t[RwEffect] = {
        [ FDDiffusesRwEffect(RwFDDiffusesEffectSetRegistered(p_sid))
        , RwToGrefRate(ItmEffectUpdateInput(RwGrefRateInputRegister(Rw_FDDiffuse_Sid(p_sid)))) ]
    }

    pure def RwFDDiffuseDiffuse(p_sid : P_Sid_t, m : RwFDDiffuseMessage, ds : RwFDDiffusesState) : Effects_t[RwEffect] = {
        ds.keys().exclude(Set(p_sid)).filter(q => ds.get(q).is_registered).fold([], (acc, q) =>
            acc.append(FDDiffusesRwEffect(RwFDDiffusesEffectAddInbox({
                p_sid   : q,
                message : m.with("sender", p_sid).with("timestamp", ds.get(q).clock)
            }))))
    }

    pure def RwFDDiffuseRelease(p_sid : P_Sid_t, index : int, d : RwFDDiffuseState) : Effects_t[RwEffect] = {
        if (index >= 0 and index < length(d.inbox)) {
            [ RwToParty(p_sid, ItmEffectUpdateIncoming(RwPartyIncomingInbox(Set(d.inbox.nth(index)))))
            , FDDiffusesRwEffect(RwFDDiffusesEffectRemainingInbox({ p_sid : p_sid
                                                                  , remaining : d.inbox.slice(0, index).concat(d.inbox.slice(index + 1, length(d.inbox))) })) ]
        } else []
    }

    pure def RwFDDiffuseContinue(p_sid : P_Sid_t, d : RwFDDiffuseState) : Effects_t[RwEffect] = {
        val nd        = d.with("clock", d.clock + 1)
        val expired   = d.inbox.select(m => RwFDDiffuseExpired(nd, m))
        val remaining = d.inbox.select(m => not(RwFDDiffuseExpired(nd, m)))
        val base      = [FDDiffusesRwEffect(RwFDDiffusesEffectIncrement(p_sid))]
        if (length(expired) == 0) base
        else base.append(FDDiffusesRwEffect(RwFDDiffusesEffectRemainingInbox({ p_sid : p_sid, remaining : remaining })))
                 .append(RwToParty(p_sid, ItmEffectUpdateIncoming(RwPartyIncomingInbox(expired.foldl(Set(), (acc, m) => acc.union(Set(m)))))))
    }

    pure def RwFDDiffuseTransition(which : RwFDDiffuseAction, p_sid : P_Sid_t, ds : RwFDDiffusesState) : Effects_t[RwEffect] = {
        match which {
            | RwFDDiffuseActionRdInput => {
                match ReadNewInput(ds.get(p_sid).itm) {
                    | Some(input_message) => {
                        (match input_message {
                            | RwFDDiffuseInputRegister      => RwFDDiffuseRegister(p_sid)
                            | RwFDDiffuseInputDiffuse(m)    => RwFDDiffuseDiffuse(p_sid, m, ds)
                            | RwFDDiffuseInputRelease(i)    => RwFDDiffuseRelease(p_sid, i, ds.get(p_sid))
                        }).append(RwToFDDiffuse(p_sid, ItmEffectPopInput))
                    }
                    | None => []
                }
            }
            | RwFDDiffuseActionRdOutput => {
                match ReadNewOutput(ds.get(p_sid).itm) {
                    | Some(output_message) => {
                        (match output_message {
                            | RwFDDiffuseOutputRegistered => [RwToParty(p_sid, ItmEffectUpdateIncoming(RwPartyIncomingRegistered))]
                            | RwFDDiffuseOutputContinue   => RwFDDiffuseContinue(p_sid, ds.get(p_sid))
                        }).append(RwToFDDiffuse(p_sid, ItmEffectPopOutput))
                    }
                    | None => []
                }
            }
        }
    }

    // -----------------------------------------------------------------

    // Relative Time Protocol (parties)
    // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    type RwPartyInput = RwPartyInputReg      // Z: join
                      | RwPartyInputRound    // Z: what slot is it?
                      | RwPartyInputOk       // Z: produce my block for this slot

    type RwPartyOutput = RwPartyOutputCurrentTime(Time_t)
                       | RwPartyOutputRegisterOk
                       | RwPartyOutputRoundOk
                       | RwPartyOutputFailed

    type RwPartyIncoming = RwPartyIncomingRegistered
                         | RwPartyIncomingInbox(Set[RwFDDiffuseMessage])
                         | RwPartyIncomingClock(Time_t)

    type RwReferencePoint = {
        round : Round_t,
        time : Time_t
    }

    type RwArrival = { sender : P_Sid_t, slot : Round_t, time : Time_t }

    type RwPartyPending = RwPendingNone
                        | RwPendingRound
                        | RwPendingOk
                        | RwPendingBlocks(Set[RwFDDiffuseMessage])

    type RwPartyState = {
        reference_point : RwReferencePoint,
        itm  : RwItm[RwPartyInput, RwPartyOutput, RwPartyIncoming],
        registered : bool,
        synced     : bool,
        arrivals   : List[RwArrival],
        pending    : RwPartyPending
    }

    type RwPartiesState = P_Sid_t -> RwPartyState

    type RwPartiesAction = RwPartiesActionRdInput | RwPartiesActionRdOutput | RwPartiesActionRdIncoming

    type RwPartiesEffect = RwPartiesEffectUpdateReference({ p_sid : P_Sid_t, reference : RwReferencePoint })
                         | RwPartiesEffectsUpdateItm({ p_sid : P_Sid_t, effect : ItmEffect[RwPartyInput, RwPartyOutput, RwPartyIncoming] })
                         | RwPartiesEffectSetRegistered({ p_sid : P_Sid_t, synced : bool })
                         | RwPartiesEffectSetSynced({ p_sid : P_Sid_t, synced : bool })
                         | RwPartiesEffectSetPending({ p_sid : P_Sid_t, pending : RwPartyPending })
                         | RwPartiesEffectSetArrivals({ p_sid : P_Sid_t, arrivals : List[RwArrival] })

    pure def RwPartiesApplyEffect(state : RwPartiesState, effect : RwPartiesEffect) : RwPartiesState = {
        match (effect) {
            | RwPartiesEffectUpdateReference(r) => state.put(r.p_sid, state.get(r.p_sid).with("reference_point", r.reference))
            | RwPartiesEffectsUpdateItm(r)      => state.put(r.p_sid, state.get(r.p_sid).with("itm", ItmApplyEffect(state.get(r.p_sid).itm, r.effect)))
            | RwPartiesEffectSetRegistered(r)   => state.put(r.p_sid, state.get(r.p_sid).with("registered", true).with("synced", r.synced))
            | RwPartiesEffectSetSynced(r)       => state.put(r.p_sid, state.get(r.p_sid).with("synced", r.synced))
            | RwPartiesEffectSetPending(r)      => state.put(r.p_sid, state.get(r.p_sid).with("pending", r.pending))
            | RwPartiesEffectSetArrivals(r)     => state.put(r.p_sid, state.get(r.p_sid).with("arrivals", r.arrivals))
        }
    }

    pure def RwPartiesInit() : RwPartiesState =
        1.to(NumberOfParties).mapBy(i => ({ reference_point : { round : FirstRound, time : TimeInit }
                                          , itm             : ItmInit(Rw_P_Sid(i))
                                          , registered      : false
                                          , synced          : false
                                          , arrivals        : []
                                          , pending         : RwPendingNone }))

    // Algorithms of the paper

    pure def RwFloorDiv(a : int, b : int) : int =
        if (a >= 0) a / b else -((-a + b - 1) / b)

    // Algorithm 1: S_Map(Π, t_curr) = sl_ref + floor((t_curr - t_ref) / T)
    pure def RwSMap(ref : RwReferencePoint, t_curr : Time_t) : Round_t =
        ref.round + RwFloorDiv(t_curr - ref.time, RoundDuration)

    // lower median of a non-empty list
    pure def RwMedian(lst : List[int]) : int = {
        val k = (length(lst) - 1) / 2
        lst.indices().map(i => lst.nth(i))
                     .filter(v => and { lst.select(x => x < v).length() <= k
                                      , lst.select(x => x <= v).length() >= k + 1 })
                     .fold(0, (acc, v) => v)
    }

    pure def RwMedianReference(arrivals : List[RwArrival]) : RwReferencePoint = {
        val sl  = arrivals.foldl(FirstRound, (acc, a) => if (a.slot > acc) a.slot else acc)
        val lst = arrivals.foldl([], (acc, a) => acc.append(a.time + (sl - a.slot) * RoundDuration))
        { round : sl, time : RwMedian(lst) }
    }

    pure def RwHasArrival(arrivals : List[RwArrival], m : RwFDDiffuseMessage) : bool =
        arrivals.select(a => and { a.sender == m.sender, a.slot == m.message.slot }).length() > 0

    pure def RwAddArrivals(arrivals : List[RwArrival], blocks : Set[RwFDDiffuseMessage], t : Time_t) : List[RwArrival] =
        blocks.fold(arrivals, (acc, m) =>
            if (and { length(acc) < SampleSize, not(RwHasArrival(acc, m)) })
                acc.append({ sender : m.sender, slot : m.message.slot, time : t })
            else acc)

    pure def RwCreateEnvSimLog(g : RwGrefRateState, l : RwFLocalsState, log : Log_t) : RwEffect =
        EnvSimRwEffect(RwEnvSimEffectLog({
            log   : log,
            reg   : l.keys().filter(k => l.get(k).is_registered),
            c     : Set(),
            ok    : g.ok,
            round : RwCurrentSlot(g)
        }))

    pure def RwPartiesRegister(p_sid : P_Sid_t) : Effects_t[RwEffect] = {
        [RwToFLocal(p_sid, ItmEffectUpdateInput(RwFLocalInputRegister))]
    }

    pure def RwPartiesAskClock(p_sid : P_Sid_t, party : RwPartyState, pending : RwPartyPending) : Effects_t[RwEffect] = {
        if (and { party.registered, party.synced })
            [ PartiesRwEffect(RwPartiesEffectSetPending({ p_sid : p_sid, pending : pending }))
            , RwToFLocal(p_sid, ItmEffectUpdateInput(RwFLocalInputGetClock)) ]
        else
            [RwToParty(p_sid, ItmEffectUpdateOutput(RwPartyOutputFailed))]
    }

    pure def RwPartiesRegistered(p_sid : P_Sid_t, g : RwGrefRateState) : Effects_t[RwEffect] = {
        [ PartiesRwEffect(RwPartiesEffectSetRegistered({ p_sid : p_sid, synced : g.counter == TimeInit }))
        , RwToParty(p_sid, ItmEffectUpdateOutput(RwPartyOutputRegisterOk)) ]
    }

    pure def RwPartiesInbox(p_sid : P_Sid_t, party : RwPartyState, blocks : Set[RwFDDiffuseMessage]) : Effects_t[RwEffect] = {
        val valid = blocks.filter(m => not(RwHasArrival(party.arrivals, m)))
        if (or { party.synced, valid.size() == 0 }) []
        else [ PartiesRwEffect(RwPartiesEffectSetPending({ p_sid : p_sid, pending : RwPendingBlocks(valid) }))
             , RwToFLocal(p_sid, ItmEffectUpdateInput(RwFLocalInputGetClock)) ]
    }

    pure def RwPartiesClock(p_sid : P_Sid_t, party : RwPartyState, t : Time_t) : Effects_t[RwEffect] = {
        val done = PartiesRwEffect(RwPartiesEffectSetPending({ p_sid : p_sid, pending : RwPendingNone }))
        match party.pending {
            | RwPendingNone => []
            | RwPendingRound => {
                [ RwToParty(p_sid, ItmEffectUpdateOutput(RwPartyOutputCurrentTime(RwSMap(party.reference_point, t))))
                , done ]
            }
            | RwPendingOk => {
                val block = { sender : p_sid, message : { slot : RwSMap(party.reference_point, t) }, timestamp : TimeInit }
                [ RwToParty(p_sid, ItmEffectUpdateOutput(RwPartyOutputRoundOk))
                , GrefRateRwEffect(RwGrefRateEffectAddOk(p_sid))
                , RwToFDDiffuse(p_sid, ItmEffectUpdateInput(RwFDDiffuseInputDiffuse(block)))
                , done ]
            }
            | RwPendingBlocks(blocks) => {
                val arrivals = RwAddArrivals(party.arrivals, blocks, t)
                if (length(arrivals) >= SampleSize)
                    [ PartiesRwEffect(RwPartiesEffectUpdateReference({ p_sid : p_sid, reference : RwMedianReference(arrivals) }))
                    , PartiesRwEffect(RwPartiesEffectSetSynced({ p_sid : p_sid, synced : true }))
                    , PartiesRwEffect(RwPartiesEffectSetArrivals({ p_sid : p_sid, arrivals : [] }))
                    , done ]
                else
                    [ PartiesRwEffect(RwPartiesEffectSetArrivals({ p_sid : p_sid, arrivals : arrivals }))
                    , done ]
            }
        }
    }

    pure def RwPartiesToZ(p_sid : P_Sid_t, response : RwPartyOutput, g : RwGrefRateState, l : RwFLocalsState) : Effects_t[RwEffect] = {
        match response {
            | RwPartyOutputCurrentTime(r) => [RwCreateEnvSimLog(g, l, LogPRound({ p_sid : p_sid, round : r }))]
            | RwPartyOutputRegisterOk     => [RwCreateEnvSimLog(g, l, LogRegOk(p_sid))]
            | RwPartyOutputRoundOk        => [RwCreateEnvSimLog(g, l, LogRoundOk(p_sid))]
            | RwPartyOutputFailed         => [RwCreateEnvSimLog(g, l, LogFailed(p_sid))]
        }
    }

    pure def RwPartiesTransition(which : RwPartiesAction, p_sid : P_Sid_t, parties : RwPartiesState, g : RwGrefRateState, l : RwFLocalsState) : Effects_t[RwEffect] = {
        val party = parties.get(p_sid)
        match which {
            | RwPartiesActionRdInput => {
                match ReadNewInput(party.itm) {
                    | Some(input_message) => {
                        (match input_message {
                            | RwPartyInputReg      => RwPartiesRegister(p_sid)
                            | RwPartyInputRound    => RwPartiesAskClock(p_sid, party, RwPendingRound)
                            | RwPartyInputOk       => RwPartiesAskClock(p_sid, party, RwPendingOk)
                        }).append(RwToParty(p_sid, ItmEffectPopInput))
                    }
                    | None => []
                }
            }
            | RwPartiesActionRdIncoming => {
                match ReadNewIncoming(party.itm) {
                    | Some(incoming_message) => {
                        (match incoming_message {
                            | RwPartyIncomingRegistered => RwPartiesRegistered(p_sid, g)
                            | RwPartyIncomingInbox(bs)  => RwPartiesInbox(p_sid, party, bs)
                            | RwPartyIncomingClock(t)   => RwPartiesClock(p_sid, party, t)
                        }).append(RwToParty(p_sid, ItmEffectPopIncoming))
                    }
                    | None => []
                }
            }
            | RwPartiesActionRdOutput => {
                match ReadNewOutput(party.itm) {
                    | Some(output_message) => {
                        RwPartiesToZ(p_sid, output_message, g, l)
                            .append(RwToParty(p_sid, ItmEffectPopOutput))
                    }
                    | None => []
                }
            }
        }
    }

    // -----------------------------------------------------------------

    // Environment and Adversary
    // ^^^^^^^^^^^^^^^^^^^^^^^^^

    type RwEnvSimState = {
        logs : Set[EnvSimLog_t]
    }

    type RwEnvSimEffect = RwEnvSimEffectLog({ log : Log_t, reg : Set[P_Sid_t], c : Set[P_Sid_t], ok : Set[P_Sid_t], round : Round_t })

    type RwEnvSimAction = RwEnvSimActionSetOk(P_Sid_t)
                        | RwEnvSimActionGetRound(P_Sid_t)
                        | RwEnvSimActionRegister(P_Sid_t)
                        | RwEnvSimActionContinue
                        | RwEnvSimActionLocalIncrease(P_Sid_t)
                        | RwEnvSimActionRelease({ p_sid : P_Sid_t, index : int })

    pure def RwEnvSimApplyEffect(state : RwEnvSimState, effect : RwEnvSimEffect) : RwEnvSimState = {
        match effect {
            | RwEnvSimEffectLog(r) => state.with("logs", EnvSimLogPush(state.logs, r.log, r.reg, r.c, r.ok, r.round))
        }
    }

    pure def RwEnvSimInit : RwEnvSimState = { logs : Set() }

    pure def RwEnvSimAllRegistered(w : RwWorld) : bool =
        w.p.keys().forall(k => w.p.get(k).registered)

    pure def RwEnvSimRegistered(w : RwWorld, p_sid : P_Sid_t) : bool =
        w.p.get(p_sid).registered

    pure def RwInboxesHaveRoom(d : RwFDDiffusesState, sender : P_Sid_t) : bool =
        d.keys().exclude(Set(sender)).forall(q => length(d.get(q).inbox) < InboxSize)

    pure def RwDriftAllowsContinue(l : RwFLocalsState) : bool =
        l.keys().forall(k => or { not(l.get(k).is_registered)
                                , and { l.get(k).local_counter + 1 <= RwMaxClock
                                      , l.get(k).local_counter + 1 - l.get(k).local_counter_z <= MaxDrift } })

    pure def RwDriftAllowsLocalIncrease(local : RwFLocalState) : bool =
        and { local.is_registered
            , local.local_counter_z + 1 <= RwMaxClock
            , local.local_counter - (local.local_counter_z + 1) >= 0 }

    pure def RwEnvSimReg(p_sid : P_Sid_t, w : RwWorld) : Effects_t[RwEffect] = {
        [ RwToParty(p_sid, ItmEffectUpdateInput(RwPartyInputReg))
        , RwCreateEnvSimLog(w.g, w.l, LogReg(p_sid)) ]
    }

    pure def RwEnvSimOk(p_sid : P_Sid_t) : Effects_t[RwEffect] =
        [RwToParty(p_sid, ItmEffectUpdateInput(RwPartyInputOk))]

    pure def RwEnvSimRound(p_sid : P_Sid_t) : Effects_t[RwEffect] =
        [RwToParty(p_sid, ItmEffectUpdateInput(RwPartyInputRound))]

    pure def RwEnvSimContinue : Effects_t[RwEffect] =
        [RwToGrefRate(ItmEffectUpdateInput(RwGrefRateInputContinue))]

    pure def RwEnvSimLocalIncrease(p_sid : P_Sid_t) : Effects_t[RwEffect] =
        [RwToFLocal(p_sid, ItmEffectUpdateInput(RwFLocalInputZIncrease))]

    pure def RwEnvSimRelease(p_sid : P_Sid_t, index : int) : Effects_t[RwEffect] =
        [RwToFDDiffuse(p_sid, ItmEffectUpdateInput(RwFDDiffuseInputRelease(index)))]

    pure def RwEnvSimTransition(which : RwEnvSimAction, zs : RwEnvSimState, idle : bool, w : RwWorld) : Effects_t[RwEffect] = {
        if (not(idle)) []
        else match which {
            | RwEnvSimActionRegister(p_sid)    => if (RwEnvSimRegistered(w, p_sid)) [] else RwEnvSimReg(p_sid, w)
            | RwEnvSimActionSetOk(p_sid)       => if (and { RwEnvSimAllRegistered(w), RwInboxesHaveRoom(w.d, p_sid) }) RwEnvSimOk(p_sid) else []
            | RwEnvSimActionGetRound(p_sid)    => if (RwEnvSimAllRegistered(w)) RwEnvSimRound(p_sid) else []
            | RwEnvSimActionContinue           => if (and { w.g.counter < RwMaxTime, RwDriftAllowsContinue(w.l) }) RwEnvSimContinue else []
            | RwEnvSimActionLocalIncrease(p_sid) => if (RwDriftAllowsLocalIncrease(w.l.get(p_sid))) RwEnvSimLocalIncrease(p_sid) else []
            | RwEnvSimActionRelease(r)         => if (and { RwEnvSimAllRegistered(w), r.index < length(w.d.get(r.p_sid).inbox) }) RwEnvSimRelease(r.p_sid, r.index) else []
        }
    }

    // -----------------------------------------------------------------

    // Main
    // ^^^^

    action RwInit = all {
        Rw_ZS'         = RwEnvSimInit,
        Rw_GrefRate'   = RwGrefRateInit,
        Rw_FLocals'    = RwFLocalsInit,
        Rw_FDDiffuses' = RwFDDiffusesInit,
        Rw_Parties'    = RwPartiesInit,
        Rw_overflow'   = false
    }

    action RwStep = {
        val w    = { zs : Rw_ZS, g : Rw_GrefRate, l : Rw_FLocals, d : Rw_FDDiffuses, p : Rw_Parties }
        val idle = RwStayIdle(w)
        nondet who = oneOf(Set( Rw_ZS_Sid
                              , Rw_GrefRate_Sid
                              , Rw_FLocal_Sid(InvalidP_Sid)
                              , Rw_FDDiffuse_Sid(InvalidP_Sid)
                              , Rw_P_Sid(InvalidP_Sid)))

        match who {
            | Rw_ZS_Sid => {
                // Environment and dummy adversary
                nondet p_sid_z = oneOf(1.to(NumberOfParties))
                nondet idx_z   = oneOf(0.to(InboxSize - 1))
                nondet which_z = oneOf(Set( RwEnvSimActionRegister(p_sid_z)
                                          , RwEnvSimActionSetOk(p_sid_z)
                                          , RwEnvSimActionGetRound(p_sid_z)
                                          , RwEnvSimActionContinue
                                          , RwEnvSimActionLocalIncrease(p_sid_z)
                                          , RwEnvSimActionRelease({ p_sid : p_sid_z, index : idx_z })))

                RwUpdate(RwEnvSimTransition(which_z, Rw_ZS, idle, w))
            }

            | Rw_P_Sid(_) => {
                // Parties
                nondet which_p = oneOf(Set( RwPartiesActionRdOutput
                                          , RwPartiesActionRdInput
                                          , RwPartiesActionRdIncoming ))
                nondet p_sid_p = oneOf(1.to(NumberOfParties))

                RwUpdate(RwPartiesTransition(which_p, p_sid_p, Rw_Parties, Rw_GrefRate, Rw_FLocals))
            }

            | Rw_FLocal_Sid(_) => {
                // F_Local
                nondet which_l = oneOf(Set( RwFLocalActionRdInput
                                          , RwFLocalActionRdOutput ))
                nondet p_sid_l = oneOf(1.to(NumberOfParties))

                RwUpdate(RwFLocalTransition(which_l, p_sid_l, Rw_FLocals))
            }

            | Rw_FDDiffuse_Sid(_) => {
                // F_DDiffuse
                nondet which_d = oneOf(Set( RwFDDiffuseActionRdInput
                                          , RwFDDiffuseActionRdOutput ))
                nondet p_sid_d = oneOf(1.to(NumberOfParties))

                RwUpdate(RwFDDiffuseTransition(which_d, p_sid_d, Rw_FDDiffuses))
            }

            | Rw_GrefRate_Sid => {
                // G_refRate
                RwUpdate(RwGrefRateTransition(RwGrefRateActionRdInput, Rw_GrefRate))
            }
        }
    }

    action RwUpdate(effects : Effects_t[RwEffect]) : bool = {
        val w = effects.foldl( { zs : Rw_ZS, g : Rw_GrefRate, l : Rw_FLocals, d : Rw_FDDiffuses, p : Rw_Parties }
                             , (acc, e) => RwApplyEffect(acc, e))

        if (RwWorldFits(w)) all {
            Rw_ZS'         = w.zs,
            Rw_GrefRate'   = w.g,
            Rw_FLocals'    = w.l,
            Rw_FDDiffuses' = w.d,
            Rw_Parties'    = w.p,
            Rw_overflow'   = Rw_overflow
        } else all {
            Rw_ZS'         = Rw_ZS,
            Rw_GrefRate'   = Rw_GrefRate,
            Rw_FLocals'    = Rw_FLocals,
            Rw_FDDiffuses' = Rw_FDDiffuses,
            Rw_Parties'    = Rw_Parties,
            Rw_overflow'   = true
        }
    }


    // -----------------------------------------------------------------

    // Properties
    // ^^^^^^^^^^

    // MUST FAIL
    // ^^^^^^^^^

    val RwSlotPastBound =
        Rw_GrefRate.counter < RwMaxTime

    // MUST PASS
    // ^^^^^^^^^

    // For correctness
    val RwNoOverflow =
        not(Rw_overflow)

    val RwTimeBounded =
        Rw_GrefRate.counter <= RwMaxTime

    val RwDriftBounded =
        Rw_FLocals.keys().forall(k => and { (Rw_FLocals.get(k).local_counter - Rw_FLocals.get(k).local_counter_z) <= MaxDrift
                                          , (Rw_FLocals.get(k).local_counter - Rw_FLocals.get(k).local_counter_z) >= 0 })

    // Theorem 7: Assuming that alpha_gamma >= (1 + epsilon) / 2, where
    // alpha_gamma is the relative stake of honest and synchronized parties, the
    // relative time protocol in the FDDiffuse, FVRF, FKES, FDSIG, FT,Sigma_local,
    // and FROhybrid models realizes GT,ThetaSlot, where Theta = Delta + 1 and |Sigma| < T.
    val RwSlotWithinTheta =
        SlotWithinOn(Rw_ZS.logs, Theta, 0)

    // proposed
    val RwSlotWithinThetaAhead =
            SlotWithinOn(Rw_ZS.logs, Theta, ThetaAhead)

    val RwGClockTimeAgreement = TimeAgreementOn(Rw_ZS.logs)

    val RwGClockTimeLiveness  = TimeLivenessOn(Rw_ZS.logs)

    val RwGClockTimeSoundness = TimeSoundnessOn(Rw_ZS.logs)
}

// -----------------------------------------------------------------

// Main
// ^^^^

module iw_main {
    import iw_gclock.* from "./gclock"

    action init = all {
        IwInit
    }

    action step = all {
        IwStep
    }
}

module rw_main {
    import rw.*

    action init = all {
        RwInit
    }

    action step = all {
        RwStep
    }
}
