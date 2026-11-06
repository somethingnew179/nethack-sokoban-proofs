import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P05B113
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 5 hero 113) = decodeDebt bits w05_113 := by
  have code : IndexedCertificateTable.get 0 rowTable (5 * stride + 113) = w05_113 := by decide +kernel
  exact packed_row rowTable horizon stride bits 5 113 w05_113 (by decide +kernel) code
theorem after_exact : (fun hero => weight 6 hero 113) = decodeDebt bits w06_113 := by
  have code : IndexedCertificateTable.get 0 rowTable (6 * stride + 113) = w06_113 := by decide +kernel
  exact packed_row rowTable horizon stride bits 6 113 w06_113 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 5) (phases.heroes 5) 113 (decodeDebt bits w05_113) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 5) (phases.heroes 5) 113 (fun hero => weight 5 hero 113) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 5) (phases.heroes 5) 113 (decodeDebt bits w05_113)
    (fun landing => weight 5 113 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 5) (phases.heroes 5) 113 (fun hero => weight 5 hero 113)
    (fun landing => weight 5 113 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 5) 113
    (decodeDebt bits w05_113) (decodeDebt bits w06_113) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 5) 113
    (fun hero => weight 5 hero 113) (fun hero => weight 6 hero 113) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P05B113
