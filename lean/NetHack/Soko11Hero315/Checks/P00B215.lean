import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P00B215
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 0 hero 215) = decodeDebt bits w00_215 := by
  have code : IndexedCertificateTable.get 0 rowTable (0 * stride + 215) = w00_215 := by decide +kernel
  exact packed_row rowTable horizon stride bits 0 215 w00_215 (by decide +kernel) code
theorem after_exact : (fun hero => weight 1 hero 215) = decodeDebt bits w01_215 := by
  have code : IndexedCertificateTable.get 0 rowTable (1 * stride + 215) = w01_215 := by decide +kernel
  exact packed_row rowTable horizon stride bits 1 215 w01_215 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 0) (phases.heroes 0) 215 (decodeDebt bits w00_215) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 0) (phases.heroes 0) 215 (fun hero => weight 0 hero 215) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 0) (phases.heroes 0) 215 (decodeDebt bits w00_215)
    (fun landing => weight 0 215 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 0) (phases.heroes 0) 215 (fun hero => weight 0 hero 215)
    (fun landing => weight 0 215 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 0) 215
    (decodeDebt bits w00_215) (decodeDebt bits w01_215) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 0) 215
    (fun hero => weight 0 hero 215) (fun hero => weight 1 hero 215) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P00B215
