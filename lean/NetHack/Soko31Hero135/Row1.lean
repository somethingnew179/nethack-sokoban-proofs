import NetHack.Soko31Hero135.Data
namespace NetHack.Soko31Hero135
open NetHack.Sokoban NetHack.Sokoban.FiniteResidual
theorem checked1 : rowCheck soko3_1.board base norm table key (List.range 348) entry1 = true := by decide +kernel
theorem bound1 : RowBound soko3_1.board base norm table key entry1 :=
  rowCheck_sound soko3_1.board base norm table key _ entry1
    (fun hero positive => finiteScore_coverage _ _ _ hero positive) checked1
end NetHack.Soko31Hero135
