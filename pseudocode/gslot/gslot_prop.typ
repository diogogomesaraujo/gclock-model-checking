#import "../fun.typ" as algorithmic
#import algorithmic: style-algorithm, algorithm-figure
#show: style-algorithm

#set page(
  height: auto,
  margin: 20pt,
)

#algorithm-figure(
  number: 3,
  [$cal(G)_"Slot"^(T, Theta, Psi)$],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Procedure(
      [Init],
      (),
      {
        Assign[$"sl"_"curr"$][$0$]
        Assign[$"counter"$][$0$]
      },
    )
    LineBreak
    Procedure(
      [Reg],
      (),
      {
        $bold("send") ("Register", "sid", cal(G)_"Slot"^(T, Theta, Psi))$
        $bold("receive") ("Registered", "sid", cal(G)_"Slot"^(T, Theta, Psi))$
      },
    )
    LineBreak
    Procedure(
      [Req_Slot],
      (),
      {
        If(
          $bold("on") ("req slot", "sid", P) "from" P$,
          $bold("send") ("req slot", "sid", P) "to" cal(A)$,
          $bold("receive") ("new slot", "sid", "sl"', P') "from" cal(A)$,
          Assign[$"sl"$][$cases(
            "sl"_"curr" & "if" "sl"_"curr" - "sl"' >= Theta "or" "sl"' - "sl"_"curr" > Psi,
            "sl"' & "otherwise"
          )$],
          $bold("send") ("current slot", "sid", "sl") "to" P$
        )
      },
    )
    LineBreak
    Procedure(
      [Counter.Incr],
      (),
      {
        If(
          $bold("on") ("Continue", "sid", cal(G)_"Slot"^(T, Theta, Psi)) "from" cal(G)_"refRate"$,
          Assign[$"counter"$][$"counter" + 1$],
          Assign[$"sl"_"curr"$][$floor("counter" / T)$]
        )
      },
    )
  }
)
