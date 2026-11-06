import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P04B239
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 4 hero 239) = decodeDebt bits w04_239 := by
  have code : IndexedCertificateTable.get 0 rowTable (4 * stride + 239) = w04_239 := by decide +kernel
  exact packed_row rowTable horizon stride bits 4 239 w04_239 (by decide +kernel) code
theorem after_exact : (fun hero => weight 5 hero 239) = decodeDebt bits w05_239 := by
  have code : IndexedCertificateTable.get 0 rowTable (5 * stride + 239) = w05_239 := by decide +kernel
  exact packed_row rowTable horizon stride bits 5 239 w05_239 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 4) (phases.heroes 4) 239 (decodeDebt bits w04_239) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 4) (phases.heroes 4) 239 (fun hero => weight 4 hero 239) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 4) (phases.heroes 4) 239 (decodeDebt bits w04_239)
    (fun landing => weight 4 239 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 4) (phases.heroes 4) 239 (fun hero => weight 4 hero 239)
    (fun landing => weight 4 239 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 4) 239
    (decodeDebt bits w04_239) (decodeDebt bits w05_239) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 4) 239
    (fun hero => weight 4 hero 239) (fun hero => weight 5 hero 239) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P04B239
