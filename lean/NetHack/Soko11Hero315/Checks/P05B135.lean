import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P05B135
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 5 hero 135) = decodeDebt bits w05_135 := by
  have code : IndexedCertificateTable.get 0 rowTable (5 * stride + 135) = w05_135 := by decide +kernel
  exact packed_row rowTable horizon stride bits 5 135 w05_135 (by decide +kernel) code
theorem after_exact : (fun hero => weight 6 hero 135) = decodeDebt bits w06_135 := by
  have code : IndexedCertificateTable.get 0 rowTable (6 * stride + 135) = w06_135 := by decide +kernel
  exact packed_row rowTable horizon stride bits 6 135 w06_135 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 5) (phases.heroes 5) 135 (decodeDebt bits w05_135) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 5) (phases.heroes 5) 135 (fun hero => weight 5 hero 135) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 5) (phases.heroes 5) 135 (decodeDebt bits w05_135)
    (fun landing => weight 5 135 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 5) (phases.heroes 5) 135 (fun hero => weight 5 hero 135)
    (fun landing => weight 5 135 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 5) 135
    (decodeDebt bits w05_135) (decodeDebt bits w06_135) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 5) 135
    (fun hero => weight 5 hero 135) (fun hero => weight 6 hero 135) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P05B135
