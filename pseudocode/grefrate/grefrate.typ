#import "../fun.typ" as algorithmic
#import algorithmic: style-algorithm, algorithm-figure
#show: style-algorithm

#set page(
  height: auto,
  margin: 20pt,
)


#algorithm-figure(
  [$cal(G)_"refRate"$],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Procedure(
      [Init],
      (),
      {
        Assign[$"ListRate"$][$emptyset$]
      },
    )
    LineBreak
    Procedure(
      [Reg],
      (),
      {
        If(
          $"receive" ("Register", "sid", P) "from" P$,
          Assign[$"ListRate"$][$"ListRate" union {P}$],
          $bold("send") ("Registered", "sid", P) "to" P$
        )
      },
    )
    LineBreak
    Procedure(
      [Continue],
      (),
      {
        If(
          $"receive" "Continue" "from" cal(Z)$,
          For(
            $P in "ListRate"$,
            $bold("send") ("Continue", "sid"', P) "to" P$
          )
        )
      },
    )
  }
)
