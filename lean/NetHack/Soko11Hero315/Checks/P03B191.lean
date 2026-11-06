import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P03B191
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 3 hero 191) = decodeDebt bits w03_191 := by
  have code : IndexedCertificateTable.get 0 rowTable (3 * stride + 191) = w03_191 := by decide +kernel
  exact packed_row rowTable horizon stride bits 3 191 w03_191 (by decide +kernel) code
theorem after_exact : (fun hero => weight 4 hero 191) = decodeDebt bits w04_191 := by
  have code : IndexedCertificateTable.get 0 rowTable (4 * stride + 191) = w04_191 := by decide +kernel
  exact packed_row rowTable horizon stride bits 4 191 w04_191 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 3) (phases.heroes 3) 191 (decodeDebt bits w03_191) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 3) (phases.heroes 3) 191 (fun hero => weight 3 hero 191) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 3) (phases.heroes 3) 191 (decodeDebt bits w03_191)
    (fun landing => weight 3 191 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 3) (phases.heroes 3) 191 (fun hero => weight 3 hero 191)
    (fun landing => weight 3 191 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 3) 191
    (decodeDebt bits w03_191) (decodeDebt bits w04_191) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 3) 191
    (fun hero => weight 3 hero 191) (fun hero => weight 4 hero 191) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P03B191
