import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P01B85
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 1 hero 85) = decodeDebt bits w01_85 := by
  have code : IndexedCertificateTable.get 0 rowTable (1 * stride + 85) = w01_85 := by decide +kernel
  exact packed_row rowTable horizon stride bits 1 85 w01_85 (by decide +kernel) code
theorem after_exact : (fun hero => weight 2 hero 85) = decodeDebt bits w02_85 := by
  have code : IndexedCertificateTable.get 0 rowTable (2 * stride + 85) = w02_85 := by decide +kernel
  exact packed_row rowTable horizon stride bits 2 85 w02_85 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 1) (phases.heroes 1) 85 (decodeDebt bits w01_85) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 1) (phases.heroes 1) 85 (fun hero => weight 1 hero 85) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 1) (phases.heroes 1) 85 (decodeDebt bits w01_85)
    (fun landing => weight 1 85 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 1) (phases.heroes 1) 85 (fun hero => weight 1 hero 85)
    (fun landing => weight 1 85 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 1) 85
    (decodeDebt bits w01_85) (decodeDebt bits w02_85) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 1) 85
    (fun hero => weight 1 hero 85) (fun hero => weight 2 hero 85) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P01B85
