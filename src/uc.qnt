// -----------------------------------------------------------------

// UC Framework
// ^^^^^^^^^^^^

module uc {
    import utils.* from "./utils"
    import assumptions.* from "./assumptions"

    type ITM[sid, in, out, in_msg] = {
        sid                : sid,
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

    pure def ItmInit(sid: sid) : ITM[sid, in, out, incoming] = {
        sid               : sid,
        input             : [],
        output            : [],
        incoming_messages : [],
    }

    pure def PopTape(tape : List[a]) : List[a] = {
        if (length(tape) == 0) tape else tape.tail()
    }

    pure def ItmApplyEffect(itm : ITM[sid, in, out, incoming], effect : ItmEffect[in, out, incoming]) : ITM[sid, in, out, incoming] = {
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

    pure def ItmIsEmpty(itm : ITM[sid, in, out, incoming]) : bool = {
        and {
            length(itm.input) == 0,
            length(itm.output) == 0,
            length(itm.incoming_messages) == 0,
        }
    }

    pure def ItmFits(itm : ITM[sid, in, out, incoming]) : bool = {
        and {
            length(itm.input) <= TapeSize,
            length(itm.output) <= TapeSize,
            length(itm.incoming_messages) <= TapeSize,
        }
    }
}
