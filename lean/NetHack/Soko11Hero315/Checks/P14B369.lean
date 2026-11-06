import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P14B369
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 14 hero 369) = decodeDebt bits w14_369 := by
  have code : IndexedCertificateTable.get 0 rowTable (14 * stride + 369) = w14_369 := by decide +kernel
  exact packed_row rowTable horizon stride bits 14 369 w14_369 (by decide +kernel) code
theorem after_exact : (fun hero => weight 15 hero 369) = decodeDebt bits w15_369 := by
  have code : IndexedCertificateTable.get 0 rowTable (15 * stride + 369) = w15_369 := by decide +kernel
  exact packed_row rowTable horizon stride bits 15 369 w15_369 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 14) (phases.heroes 14) 369 (decodeDebt bits w14_369) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 14) (phases.heroes 14) 369 (fun hero => weight 14 hero 369) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 14) (phases.heroes 14) 369 (decodeDebt bits w14_369)
    (fun landing => weight 14 369 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 14) (phases.heroes 14) 369 (fun hero => weight 14 hero 369)
    (fun landing => weight 14 369 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 14) 369
    (decodeDebt bits w14_369) (decodeDebt bits w15_369) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 14) 369
    (fun hero => weight 14 hero 369) (fun hero => weight 15 hero 369) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P14B369
