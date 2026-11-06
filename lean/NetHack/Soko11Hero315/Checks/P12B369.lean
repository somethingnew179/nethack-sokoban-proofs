import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P12B369
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 12 hero 369) = decodeDebt bits w12_369 := by
  have code : IndexedCertificateTable.get 0 rowTable (12 * stride + 369) = w12_369 := by decide +kernel
  exact packed_row rowTable horizon stride bits 12 369 w12_369 (by decide +kernel) code
theorem after_exact : (fun hero => weight 13 hero 369) = decodeDebt bits w13_369 := by
  have code : IndexedCertificateTable.get 0 rowTable (13 * stride + 369) = w13_369 := by decide +kernel
  exact packed_row rowTable horizon stride bits 13 369 w13_369 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 12) (phases.heroes 12) 369 (decodeDebt bits w12_369) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 12) (phases.heroes 12) 369 (fun hero => weight 12 hero 369) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 12) (phases.heroes 12) 369 (decodeDebt bits w12_369)
    (fun landing => weight 12 369 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 12) (phases.heroes 12) 369 (fun hero => weight 12 hero 369)
    (fun landing => weight 12 369 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 12) 369
    (decodeDebt bits w12_369) (decodeDebt bits w13_369) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 12) 369
    (fun hero => weight 12 hero 369) (fun hero => weight 13 hero 369) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P12B369
