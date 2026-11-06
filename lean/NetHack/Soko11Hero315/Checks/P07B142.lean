import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P07B142
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 7 hero 142) = decodeDebt bits 0 := by
  have code : IndexedCertificateTable.get 0 rowTable (7 * stride + 142) = 0 := by decide +kernel
  exact packed_row rowTable horizon stride bits 7 142 0 (by decide +kernel) code
theorem after_exact : (fun hero => weight 8 hero 142) = decodeDebt bits 0 := by
  have code : IndexedCertificateTable.get 0 rowTable (8 * stride + 142) = 0 := by decide +kernel
  exact packed_row rowTable horizon stride bits 8 142 0 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 7) (phases.heroes 7) 142 (decodeDebt bits 0) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 7) (phases.heroes 7) 142 (fun hero => weight 7 hero 142) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 7) (phases.heroes 7) 142 (decodeDebt bits 0)
    (fun landing => weight 7 142 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 7) (phases.heroes 7) 142 (fun hero => weight 7 hero 142)
    (fun landing => weight 7 142 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 7) 142
    (decodeDebt bits 0) (decodeDebt bits 0) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 7) 142
    (fun hero => weight 7 hero 142) (fun hero => weight 8 hero 142) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P07B142
