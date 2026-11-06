import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P09B296
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 9 hero 296) = decodeDebt bits w09_296 := by
  have code : IndexedCertificateTable.get 0 rowTable (9 * stride + 296) = w09_296 := by decide +kernel
  exact packed_row rowTable horizon stride bits 9 296 w09_296 (by decide +kernel) code
theorem after_exact : (fun hero => weight 10 hero 296) = decodeDebt bits w10_296 := by
  have code : IndexedCertificateTable.get 0 rowTable (10 * stride + 296) = w10_296 := by decide +kernel
  exact packed_row rowTable horizon stride bits 10 296 w10_296 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 9) (phases.heroes 9) 296 (decodeDebt bits w09_296) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 9) (phases.heroes 9) 296 (fun hero => weight 9 hero 296) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 9) (phases.heroes 9) 296 (decodeDebt bits w09_296)
    (fun landing => weight 9 296 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 9) (phases.heroes 9) 296 (fun hero => weight 9 hero 296)
    (fun landing => weight 9 296 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 9) 296
    (decodeDebt bits w09_296) (decodeDebt bits w10_296) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 9) 296
    (fun hero => weight 9 hero 296) (fun hero => weight 10 hero 296) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P09B296
