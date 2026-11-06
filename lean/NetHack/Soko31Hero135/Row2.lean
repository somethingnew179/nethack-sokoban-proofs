import NetHack.Soko31Hero135.Data
namespace NetHack.Soko31Hero135
open NetHack.Sokoban NetHack.Sokoban.FiniteResidual
theorem checked2 : rowCheck soko3_1.board base norm table key (List.range 348) entry2 = true := by decide +kernel
theorem bound2 : RowBound soko3_1.board base norm table key entry2 :=
  rowCheck_sound soko3_1.board base norm table key _ entry2
    (fun hero positive => finiteScore_coverage _ _ _ hero positive) checked2
end NetHack.Soko31Hero135
