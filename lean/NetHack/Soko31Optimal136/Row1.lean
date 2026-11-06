import NetHack.Soko31Optimal136.Data
namespace NetHack.Soko31Optimal136
open NetHack.Sokoban NetHack.Sokoban.FiniteResidual
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked1 : rowCheck soko3_1.board base norm table key (List.range 348) entry1 = true := by decide +kernel
theorem bound1 : RowBound soko3_1.board base norm table key entry1 :=
  rowCheck_sound soko3_1.board base norm table key _ entry1
    (fun hero positive => finiteScore_coverage _ _ _ hero positive) checked1
end NetHack.Soko31Optimal136
