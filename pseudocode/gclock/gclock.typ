#import "../lib.typ" as algorithmic
#import algorithmic: style-algorithm, algorithm-figure
#show: style-algorithm

#set page(
  height: auto,
  margin: 20pt,
)


#algorithm-figure(
  [$cal(G)$-Clock[P]],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Procedure(
      "Init",
      (),
      {
        Assign[$r$][$0$]
        Assign[$bold("Reg")$][$emptyset$]
        Assign[$bold("Done")[*]$][$0$]
      },
    )
    LineBreak
    Procedure(
      [$P_"sid"."Reg"$],
      (),
      {
        Comment[any sid]
        Assign[$bold("Reg")$][$bold("Reg") union {P_"sid"}$]
        If($P_"sid" in.not bold("Reg")$,
          {
            Assign[$bold("Done")[P_"sid"]$][$0$]
          })
        Return("ok")
      },
    )
    LineBreak
    Procedure(
      [$P_"sid"."Round"$],
      (),
      {
        Comment[any sid]
        Return("r")
      },
    )
    LineBreak
    Procedure(
      [Sim$."Round"$],
      (),
      {
        Return("r")
      },
    )
    LineBreak
    Procedure(
      [Sim$."Corrupt"$],
      $P_"sid"$,
      {
        Comment[any sid]
        Assign[$bold(C)$][$bold(C) union {P_"sid"}$]
      },
    )
    LineBreak
    Procedure(
      [$P_"sid"."Ok"$],
      (),
      {
        Comment[any sid]
        If($P_"sid" in.not bold("Reg")$,
          {
            Return($bot$)
          })
        Assign[$bold("Done")[P_"sid"]$][$1$]
        Assign[flag][$1$]
        For(
          $P'_"sid"' in bold("Reg") without bold("C")$,
          If(
            $bold("Done")[P'_"sid"'] = 0$,
            Assign[flag][$0$]
          )
        )
        If(
          $"flag" = 1$,
          Assign[$r$][$r + 1$],
          For(
            $P'_"sid"' in bold("Reg") without bold("C")$,
             Assign[$bold("Done")[P'_"sid"']$][$0$]
          )
        )
        Call("Sim", $P_"sid"."OK"$)
        Return("ok")
      },
    )
  }
)
