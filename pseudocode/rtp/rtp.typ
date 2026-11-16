#import "../protocol.typ" as algorithmic
#import algorithmic: style-algorithm, algorithm-figure
#show: style-algorithm

#set page(
  height: auto,
  margin: 20pt,
)


#algorithm-figure(
  [Ouroboros Clepsydra (Real Time Protocol)],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Procedure(
      "S_Map",
      ($bold(Pi)$, $t_"curr"$),
      {
        Assign[$bold(Pi)$][$("sl"_"ref", t_"ref")$]
        Assign[$"dif"$][$floor((t_"curr" - t_"ref") / T)$]
        Return($"sl"_"ref" + "dif"$)
      },
    )
    LineBreak
    Procedure(
      [maxvalid],
      ($cal(C)$, $C_"best"$),
      {
        Assign[$C_"max"$][$C_"best"$]
        For(
          $C_"cand" in cal(C)$,
          If(
            $C_"cand" gt C_"max" and C^("⌜" k)_"best" prec.eq C_"cand"$,
            Assign[$C_"max"$][$C_"cand"$]
          )
        )
        Return($C_"max"$)
      },
    )
    LineBreak
    Procedure(
      [Median],
      ("sl"),
      {
        Assign[$"lst"$][$emptyset$]
        For(
          $i = 0 "to" n$,
          Assign[$a_i$][$"sl" - "sl"'_i$],
          $bold("store") (t_i + a_i T) "in" "lst"$
        )
        Assign[lst][$mono("sort")("lst")$]
        Return($mono("median")("lst")$)
      },
    )
    LineBreak
    Procedure(
      [RelativeTime],
      (),
      {
        Assign[$"arr"$][$emptyset$]
        While(
          $|"arr"| < n$,
          $bold("wait for valid block") B'_i "with" "sl"'_i$,
          Assign[$t_i$][$bold("Get Clock") "from" cal(F)_"local"^(Sigma, P)$],
          $bold("store") ("sl"'_i, t_i) "in" "arr"$
        )
        Assign[$"sl"_"max"$][$max_i "sl"'_i$]
        Assign[$"sl"$][$"any value" gt.eq "sl"_"max"$]
        Assign[$t_"sl"$][$"Median"("sl")$]
        Assign[$bold(Pi)$][$("sl", t_"sl")$]
        Return($bold(Pi)$)
      },
    )
  }
)
