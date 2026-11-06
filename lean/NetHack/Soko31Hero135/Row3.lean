import NetHack.Soko31Hero135.Data
namespace NetHack.Soko31Hero135
open NetHack.Sokoban NetHack.Sokoban.FiniteResidual
theorem checked3 : rowCheck soko3_1.board base norm table key (List.range 348) entry3 = true := by decide +kernel
theorem bound3 : RowBound soko3_1.board base norm table key entry3 :=
  rowCheck_sound soko3_1.board base norm table key _ entry3
    (fun hero positive => finiteScore_coverage _ _ _ hero positive) checked3
end NetHack.Soko31Hero135
