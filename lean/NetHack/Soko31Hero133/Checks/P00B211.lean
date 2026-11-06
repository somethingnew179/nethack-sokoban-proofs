import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P00B211
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 0 hero 211) = decodeDebt bits w00_211 := by
  have code : IndexedCertificateTable.get 0 rowTable (0 * stride + 211) = w00_211 := by decide +kernel
  exact packed_row rowTable horizon stride bits 0 211 w00_211 (by decide +kernel) code
theorem after_exact : (fun hero => weight 1 hero 211) = decodeDebt bits w01_211 := by
  have code : IndexedCertificateTable.get 0 rowTable (1 * stride + 211) = w01_211 := by decide +kernel
  exact packed_row rowTable horizon stride bits 1 211 w01_211 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 0) (phases.heroes 0) 211 (decodeDebt bits w00_211) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 0) (phases.heroes 0) 211 (fun hero => weight 0 hero 211) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 0) (phases.heroes 0) 211 (decodeDebt bits w00_211)
    (fun landing => weight 0 211 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 0) (phases.heroes 0) 211 (fun hero => weight 0 hero 211)
    (fun landing => weight 0 211 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 0) 211
    (decodeDebt bits w00_211) (decodeDebt bits w01_211) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 0) 211
    (fun hero => weight 0 hero 211) (fun hero => weight 1 hero 211) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P00B211
