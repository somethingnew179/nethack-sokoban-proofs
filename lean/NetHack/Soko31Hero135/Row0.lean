import NetHack.Soko31Hero135.Data
namespace NetHack.Soko31Hero135
open NetHack.Sokoban NetHack.Sokoban.FiniteResidual
theorem checked0 : rowCheck soko3_1.board base norm table key (List.range 348) entry0 = true := by decide +kernel
theorem bound0 : RowBound soko3_1.board base norm table key entry0 :=
  rowCheck_sound soko3_1.board base norm table key _ entry0
    (fun hero positive => finiteScore_coverage _ _ _ hero positive) checked0
end NetHack.Soko31Hero135
