import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P05B318
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 5 hero 318) = decodeDebt bits w05_318 := by
  have code : IndexedCertificateTable.get 0 rowTable (5 * stride + 318) = w05_318 := by decide +kernel
  exact packed_row rowTable horizon stride bits 5 318 w05_318 (by decide +kernel) code
theorem after_exact : (fun hero => weight 6 hero 318) = decodeDebt bits w06_318 := by
  have code : IndexedCertificateTable.get 0 rowTable (6 * stride + 318) = w06_318 := by decide +kernel
  exact packed_row rowTable horizon stride bits 6 318 w06_318 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 5) (phases.heroes 5) 318 (decodeDebt bits w05_318) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 5) (phases.heroes 5) 318 (fun hero => weight 5 hero 318) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 5) (phases.heroes 5) 318 (decodeDebt bits w05_318)
    (fun landing => weight 5 318 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 5) (phases.heroes 5) 318 (fun hero => weight 5 hero 318)
    (fun landing => weight 5 318 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 5) 318
    (decodeDebt bits w05_318) (decodeDebt bits w06_318) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 5) 318
    (fun hero => weight 5 hero 318) (fun hero => weight 6 hero 318) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P05B318
