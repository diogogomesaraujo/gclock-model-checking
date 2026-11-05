<div align="center">
  <h3 align="center">gclock-model-checking</h3>
  <p align="center">
    Model-Checking the UC-Realizability of the G-Clock Ideal Functionality in the Real World with Quint
  </p>
</div>

## About 

This project is being developed as part of my MsC thesis in Computer Science at Faculdade de Ciências da Universidade do Porto, entitled _From Ideal Clocks to Buildable Ones_. The goal is to verify if real-world distributed protocols can satisfy the _G-Clock_ ideal functionality.

## UC-framework

We follow the Dummy Adversary variant of UC where the definition of security is the following:

We say that a protocol Pi realizes a functionality F with respect to the dummy adversary A if there exists an ideal-world simulator S such that, for every environment Z: IDEAL(S, Z, F) ≈ EXEC(Pi, A, Z).

### In Quint

To model this in Quint, each machine has a state record containing its input, output, and incoming-message tapes, along with a session identifier (sid):

```quint
type ITM[in, out, in_msg] = {
    sid                : Sid_t,
    input              : List[in],
    output             : List[out],
    incoming_messages  : List[in_msg],
}
```

Depending on if a machine is a child/parent of another one, or if it corresponds to a global functionality, it has different rules for which machines can it write to and who can to it:
- All communication received from the protocol participants are forwarded directly to the environment Z. That is, when A receives incoming m from party P, it simply writes "received m from P" on the subroutine tape of Z.
- It sends messages from the adversary to the parties, as directed. That is, when A receives "send m to P" from Z, it writes m on the incoming message tape of party P.
- Parties can write directly to the global functionality’s input tape, and the functionality can write to the parties’ output tapes.

## Ideal World

The ideal-world model has three main components:
- **Environment (ZS):** Registers parties, submits Round and OK requests on behalf of the parties, and coordinates the simulator by forwarding messages between them and the G-Clock functionality.
- **G-Clock:** Tracks registered parties, corruptions, readiness, and the current round.
- **Parties (P):** Forward requests to the clock and return its responses.

### G-Clock

The G-Clock ideal functionality is the same as the one from _Crossing with Confidence: Formal Analysis and Model Checking of Blockchain Bridges_:

![image](pseudocode/gclock/gclock.svg)

The clock maintains a round counter, a set of registered parties, a set of corrupted parties, and a readiness flag (done) for each party.

### Properties

To prove the G-Clock's correctness, the following properties where checked (mostly based on the _Crossing with Confidence: Formal_ paper).


#### Time Agreement

_If two parties query the time and no OK requests have been sent in the middle then G-clock responds with the same time._

#### Time Liveness
_If all registered honest parties are ready, then time advances._

#### Time Soundness
_If time advanced then all currently registered honest parties were ready._

#### Results

All tests were ran on a M4 Macbook Air with 16GB of RAM using the TLC backend and Quint 0.32.0. 

<table>
  <thead>
    <tr>
      <th>Property</th>
      <th>Parties</th>
      <th>Corrupted</th>
      <th>Rounds</th>
      <th>Verification Time</th>
      <th>Distinct States Generated</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td>Time Agreement</td>
      <td>3</td>
      <td>1</td>
      <td>5</td>
      <td>21s</td>
      <td>492 928</td>
    </tr>
    <tr>
      <td>Time Liveness</td>
      <td>3</td>
      <td>1</td>
      <td>5</td>
      <td>21s</td>
      <td>492 928</td>
    </tr>
    <tr>
      <td>Time Soundness</td>
      <td>3</td>
      <td>1</td>
      <td>5</td>
      <td>21s</td>
      <td>492 928</td>
    </tr>
  </tbody>
</table>


## Real World

Work in progress.

## References
- [UC framework and rules](https://swayam-padhy.gitbook.io/)
- [GClock Model Cheching](https://eprint.iacr.org/2026/292.pdf)
- [UC Synchrony and adaptive corruption](https://eprint.iacr.org/2011/310.pdf)
- [Quint cheatsheet](https://quint.sh/quint-cheatsheet.pdf)
