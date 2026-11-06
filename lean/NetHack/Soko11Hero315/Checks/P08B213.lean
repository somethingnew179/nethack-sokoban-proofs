import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P08B213
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 8 hero 213) = decodeDebt bits w08_213 := by
  have code : IndexedCertificateTable.get 0 rowTable (8 * stride + 213) = w08_213 := by decide +kernel
  exact packed_row rowTable horizon stride bits 8 213 w08_213 (by decide +kernel) code
theorem after_exact : (fun hero => weight 9 hero 213) = decodeDebt bits w09_213 := by
  have code : IndexedCertificateTable.get 0 rowTable (9 * stride + 213) = w09_213 := by decide +kernel
  exact packed_row rowTable horizon stride bits 9 213 w09_213 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 8) (phases.heroes 8) 213 (decodeDebt bits w08_213) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 8) (phases.heroes 8) 213 (fun hero => weight 8 hero 213) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 8) (phases.heroes 8) 213 (decodeDebt bits w08_213)
    (fun landing => weight 8 213 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 8) (phases.heroes 8) 213 (fun hero => weight 8 hero 213)
    (fun landing => weight 8 213 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 8) 213
    (decodeDebt bits w08_213) (decodeDebt bits w09_213) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 8) 213
    (fun hero => weight 8 hero 213) (fun hero => weight 9 hero 213) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P08B213
