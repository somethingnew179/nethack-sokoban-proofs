import NetHack.Soko31Optimal136.Data
namespace NetHack.Soko31Optimal136
open NetHack.Sokoban NetHack.Sokoban.FiniteResidual
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked3 : rowCheck soko3_1.board base norm table key (List.range 348) entry3 = true := by decide +kernel
theorem bound3 : RowBound soko3_1.board base norm table key entry3 :=
  rowCheck_sound soko3_1.board base norm table key _ entry3
    (fun hero positive => finiteScore_coverage _ _ _ hero positive) checked3
end NetHack.Soko31Optimal136
