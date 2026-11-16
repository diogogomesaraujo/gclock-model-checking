#import "../fun.typ" as algorithmic
#import algorithmic: style-algorithm, algorithm-figure
#show: style-algorithm

#set page(
  height: auto,
  margin: 20pt,
)


#algorithm-figure(
  [$cal(F)_"DDiffuse"^T$],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Procedure(
      [Init],
      (),
      {
        Assign[$ℓ$][$0$]
        Assign[$"inbox"_i$][$emptyset$]
        Assign[$"delayed"_i$][$emptyset$]
      },
    )
    LineBreak
    Procedure(
      [Reg],
      (),
      {
        $bold("send") ("Register", "sid", cal(F)_"DDiffuse") "to" cal(G)_"refRate"$
        $bold("receive") ("Registered", "sid", cal(F)_"DDiffuse")$
      },
    )
    LineBreak
    Procedure(
      [Diffuse],
      (),
      {
        If(
          $"receive" ("Diffuse", "sid", m) "from" P_j$,
          $bold("send") m "to" cal(A)$,
          $cal(A) "either moves" m "to" "inbox"_i "or labels it" "delayed"_i$
        )
      },
    )
    LineBreak
    Procedure(
      [Delay],
      (),
      {
        If(
          $"receive" "delayed"_i "for" m "from" cal(A)$,
          Assign[$"delayed"_i$][$"delayed"_i union {(m, ℓ)}$]
        )
      },
    )
    LineBreak
    Procedure(
      [Deliver],
      (),
      {
        If(
          $(m, ℓ_m) in "delayed"_i: cal(A) "releases" m "or" ℓ gt.eq ℓ_m + Delta T$,
          Assign[$"inbox"_i$][$"inbox"_i union {m}$],
          Assign[$"delayed"_i$][$"delayed"_i backslash {(m, ℓ_m)}$]
        )
      },
    )
    LineBreak
    Procedure(
      [Fetch],
      (),
      {
        If(
          $"receive" "Fetch" "from" P_i$,
          $bold("send") "inbox"_i "to" P_i$
        )
      },
    )
    LineBreak
    Procedure(
      [Continue],
      (),
      {
        If(
          $"receive" "Continue" "from" cal(G)_"refRate"$,
          Assign[$ℓ$][$ℓ + 1$]
        )
      },
    )
  }
)
