import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P03B291
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 3 hero 291) = decodeDebt bits w03_291 := by
  have code : IndexedCertificateTable.get 0 rowTable (3 * stride + 291) = w03_291 := by decide +kernel
  exact packed_row rowTable horizon stride bits 3 291 w03_291 (by decide +kernel) code
theorem after_exact : (fun hero => weight 4 hero 291) = decodeDebt bits w04_291 := by
  have code : IndexedCertificateTable.get 0 rowTable (4 * stride + 291) = w04_291 := by decide +kernel
  exact packed_row rowTable horizon stride bits 4 291 w04_291 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 3) (phases.heroes 3) 291 (decodeDebt bits w03_291) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 3) (phases.heroes 3) 291 (fun hero => weight 3 hero 291) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 3) (phases.heroes 3) 291 (decodeDebt bits w03_291)
    (fun landing => weight 3 291 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 3) (phases.heroes 3) 291 (fun hero => weight 3 hero 291)
    (fun landing => weight 3 291 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 3) 291
    (decodeDebt bits w03_291) (decodeDebt bits w04_291) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 3) 291
    (fun hero => weight 3 hero 291) (fun hero => weight 4 hero 291) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P03B291
