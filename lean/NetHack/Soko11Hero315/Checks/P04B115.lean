import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P04B115
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 4 hero 115) = decodeDebt bits w04_115 := by
  have code : IndexedCertificateTable.get 0 rowTable (4 * stride + 115) = w04_115 := by decide +kernel
  exact packed_row rowTable horizon stride bits 4 115 w04_115 (by decide +kernel) code
theorem after_exact : (fun hero => weight 5 hero 115) = decodeDebt bits w05_115 := by
  have code : IndexedCertificateTable.get 0 rowTable (5 * stride + 115) = w05_115 := by decide +kernel
  exact packed_row rowTable horizon stride bits 5 115 w05_115 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 4) (phases.heroes 4) 115 (decodeDebt bits w04_115) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 4) (phases.heroes 4) 115 (fun hero => weight 4 hero 115) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 4) (phases.heroes 4) 115 (decodeDebt bits w04_115)
    (fun landing => weight 4 115 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 4) (phases.heroes 4) 115 (fun hero => weight 4 hero 115)
    (fun landing => weight 4 115 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 4) 115
    (decodeDebt bits w04_115) (decodeDebt bits w05_115) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 4) 115
    (fun hero => weight 4 hero 115) (fun hero => weight 5 hero 115) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P04B115
