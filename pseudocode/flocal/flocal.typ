#import "../fun.typ" as algorithmic
#import algorithmic: style-algorithm, algorithm-figure
#show: style-algorithm

#set page(
  height: auto,
  margin: 20pt,
)


#algorithm-figure(
  number: 3,
  [$cal(F)_"local"^(Sigma, P)$],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Procedure(
      [Init],
      (),
      {
        Assign[$"localclock"_cal(Z)$][$"counter"$]
        Assign[$"localclock"$][$"counter"$]
      },
    )
    LineBreak
    Procedure(
      [Reg],
      (),
      {
        $bold("send") ("Register", "sid", cal(G)_"Slot"^(T, Theta))$
        $bold("receive") ("Registered", "sid", P)$
      },
    )
    LineBreak
    Procedure(
      [$"localclock"_cal(Z)$.Incr],
      (),
      {
        If(
          $bold("on") ("Increase", "sid", P) "from" cal(Z)$,
          Assign[$"localclock"_cal(Z)$][$"localclock"_cal(Z) + 1$],
          Assign[$Sigma$][$"localclock" - "localclock"_cal(Z)$]
        )
      },
    )
    LineBreak
    Procedure(
      [$"localclock"$.Incr],
      (),
      {
        If(
          $bold("on") ("Continue", "sid", cal(F)_"local") "from" cal(G)_"refRate"$,
          Assign[$"localclock"$][$"localclock" + 1$],
          Assign[$Sigma$][$"localclock" - "localclock"_cal(Z)$]
        )
      },
    )
    LineBreak
    Procedure(
      [Get_Clock],
      (),
      {
        If(
          $bold("on") ("get clock", "sid", P) "from" P$,
          $bold("send") ("clock", "sid", "localclock"_cal(Z), P)$
        )
      },
    )
  }
)
