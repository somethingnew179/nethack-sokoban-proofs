import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P04B322
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 4 hero 322) = decodeDebt bits 0 := by
  have code : IndexedCertificateTable.get 0 rowTable (4 * stride + 322) = 0 := by decide +kernel
  exact packed_row rowTable horizon stride bits 4 322 0 (by decide +kernel) code
theorem after_exact : (fun hero => weight 5 hero 322) = decodeDebt bits 0 := by
  have code : IndexedCertificateTable.get 0 rowTable (5 * stride + 322) = 0 := by decide +kernel
  exact packed_row rowTable horizon stride bits 5 322 0 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 4) (phases.heroes 4) 322 (decodeDebt bits 0) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 4) (phases.heroes 4) 322 (fun hero => weight 4 hero 322) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 4) (phases.heroes 4) 322 (decodeDebt bits 0)
    (fun landing => weight 4 322 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 4) (phases.heroes 4) 322 (fun hero => weight 4 hero 322)
    (fun landing => weight 4 322 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 4) 322
    (decodeDebt bits 0) (decodeDebt bits 0) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 4) 322
    (fun hero => weight 4 hero 322) (fun hero => weight 5 hero 322) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P04B322
