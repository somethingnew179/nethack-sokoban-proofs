import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P00B164
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 0 hero 164) = decodeDebt bits w00_164 := by
  have code : IndexedCertificateTable.get 0 rowTable (0 * stride + 164) = w00_164 := by decide +kernel
  exact packed_row rowTable horizon stride bits 0 164 w00_164 (by decide +kernel) code
theorem after_exact : (fun hero => weight 1 hero 164) = decodeDebt bits w01_164 := by
  have code : IndexedCertificateTable.get 0 rowTable (1 * stride + 164) = w01_164 := by decide +kernel
  exact packed_row rowTable horizon stride bits 1 164 w01_164 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 0) (phases.heroes 0) 164 (decodeDebt bits w00_164) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 0) (phases.heroes 0) 164 (fun hero => weight 0 hero 164) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 0) (phases.heroes 0) 164 (decodeDebt bits w00_164)
    (fun landing => weight 0 164 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 0) (phases.heroes 0) 164 (fun hero => weight 0 hero 164)
    (fun landing => weight 0 164 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 0) 164
    (decodeDebt bits w00_164) (decodeDebt bits w01_164) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 0) 164
    (fun hero => weight 0 hero 164) (fun hero => weight 1 hero 164) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P00B164
