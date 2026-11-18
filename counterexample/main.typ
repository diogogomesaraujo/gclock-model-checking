#show raw: set text(size: 8.8pt)

#let seq = math.class("binary", ".")
#let dia(x) = $lr(chevron.l #x chevron.r)$
#let pr(id, body: none) = link(label("prop-" + id), if body == none { id } else { body })

#set page(numbering: "1")

#show math.equation.where(block: true): it => pad(left: 1em, align(left, it))

#set par(
  justify: true,
)

#align(center)[
  #text(size: 18pt, weight: "bold")[
    A Counterexample to the UC Security of Ouroboros Clepsydra's Real Time Protocol
  ]

  #text[Diogo Araújo]

  #text[DCC, FCUP]

  #text[#datetime.today().display("[month repr:long] [year]")]
]

= Introduction

Proof-of-Stake (PoS) protocols in the Ouroboros family are provably secure under the assumption that all parties are synchronized and operate in lockstep rounds. However, this assumption does not hold in real-world settings, where parties rely on independent local clocks that may drift and communicate over potentially unreliable networks.

Previous work has sought to address this limitation @badertscher2019ouroboros @alper2019ouroboros, establishing security under weaker and more realistic timing models. In this work, we focus on Ouroboros Clepsydra @alper2019ouroboros and, in particular, the security proof of its Real Time Protocol. Using model checking with Quint, we identify a counterexample that challenges the protocol's security guarantees and may reveal a flaw in its proof.

= Preliminaries

== The UC model

The Universal Composability (UC) framework @canetti2001universally compares a protocol to an ideal functionality. Protocols are systems of interactive Turing machines (ITMs) and a running instance of an ITM is an ITI, identified by a session identifier $"sid"$ and a party identifier $P$. An environment $cal(Z)$ chooses the inputs, activates the parties and the adversary, and finally outputs a bit. A protocol is secure if $cal(Z)$ cannot tell the real execution from the ideal one.

Two ensembles $X$ and $Y$ are _computationally indistinguishable_, written $X approx Y$, if no probabilistic polynomial-time (PPT) distinguisher tells them apart with more than negligible advantage in the security parameter $kappa$.

*Real world:* On input $z in {0,1}^*$ and security parameter $kappa$, $cal(Z)$ activates the parties running $pi$ and an adversary $cal(A)$. All messages between parties pass through $cal(A)$, which may corrupt parties. We write $"EXEC"_(pi, cal(A), cal(Z))$ for the ensemble of $cal(Z)$'s outputs, over all $kappa$ and $z$.

*Ideal world:* The parties are dummy parties that forward their inputs to an incorruptible ideal functionality $cal(F)$, which carries out the task. The adversary is a simulator $cal(S)$, which interacts with $cal(F)$ in the way the code of $cal(F)$ allows. The corresponding ensemble is $"EXEC"_(cal(F), cal(S), cal(Z))$.

*Hybrid world:* In the $cal(G)$-hybrid world, the parties of $pi$ also have access to an ideal functionality $cal(G)$. This is how we model the building blocks of a protocol, such as a network or a clock.

#block[
  *Definition 1 (UC realization).* A protocol $pi$ _UC-realizes_ $cal(F)$ if for every PPT adversary $cal(A)$ there is a PPT simulator $cal(S)$ such that for every PPT environment $cal(Z)$
  $ "EXEC"_(pi, cal(A), cal(Z)) approx "EXEC"_(cal(F), cal(S), cal(Z)). $
]

By the UC composition theorem @canetti2001universally, a protocol that realizes $cal(F)$ can replace $cal(F)$ in any protocol that uses it.

== The dummy adversary

The dummy adversary $cal(A)_D$ is a fixed adversary that only relays messages. It forwards everything it receives from the parties to $cal(Z)$, and delivers to a party whatever $cal(Z)$ tells it to send. It also corrupts parties only when $cal(Z)$ says so. All adversarial behavior is therefore decided by $cal(Z)$.

#block[
  *Theorem 1 @canetti2001universally.* $pi$ UC-realizes $cal(F)$ if and only if there is a simulator $cal(S)$ such that for every environment $cal(Z)$
  $ "EXEC"_(pi, cal(A)_D, cal(Z)) approx "EXEC"_(cal(F), cal(S), cal(Z)). $
]

It is therefore enough to consider the dummy adversary. In our model, $cal(Z)$ plays the adversary: it triggers every adversarial action, such as message delays, corruptions and the choices left to the adversary in $cal(F)$.

== Global setup and time

Standard UC treats each session in isolation. The Generalized UC (GUC) model @badertscher2020universal allows a _global_ functionality $cal(G)$ shared by all sessions and protocols. Here $cal(Z)$ can interact with $cal(G)$ directly, which models setups that exist beyond a single protocol instance, such as a clock. A UC treatment of network time is given in @canetti2017universally.

= Model

= Claim

= Counterexample

= A New $bold(cal(G)_"Slot")$

#bibliography("works.bib")
