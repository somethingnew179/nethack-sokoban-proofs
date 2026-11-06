import NetHack.Soko22Hazard87.Numeric003
import NetHack.Soko22Hazard87.AndIntroBlocks0057
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric280 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 102 p
  rw [at102] at beforeRange
  have afterRange := bonus_range 125 (HazardPattern.afterPattern 10000 p (.walk 125))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ∧ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ≤ 2 at afterRange
  rw [gammaAfter280] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local280 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 125) + NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) + bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 125) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 102 p at decreasing
  rw [gammaAfter280, at102] at decreasing
  have numeric := numeric280 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125))
  rw [oldBefore102, at102, literal, oldAfter280, gammaAfter280]
  exact numeric
theorem numeric281 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 102 p
  rw [at102] at beforeRange
  have afterRange := bonus_range 123 (HazardPattern.afterPattern 10000 p (.walk 123))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ∧ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ≤ 2 at afterRange
  rw [gammaAfter281] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local281 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 123) + NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) + bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 123) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 102 p at decreasing
  rw [gammaAfter281, at102] at decreasing
  have numeric := numeric281 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123))
  rw [oldBefore102, at102, literal, oldAfter281, gammaAfter281]
  exact numeric
theorem numeric282 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 103 p
  rw [at103] at beforeRange
  have afterRange := bonus_range 81 (HazardPattern.afterPattern 10000 p (.walk 81))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) ∧ bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) ≤ 2 at afterRange
  rw [gammaAfter282] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local282 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 81 (HazardPattern.afterPattern 10000 p (.walk 81)) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 81) + NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 81))) + bonus 81 (HazardPattern.afterPattern 10000 p (.walk 81)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 81) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) < bonus 103 p at decreasing
  rw [gammaAfter282, at103] at decreasing
  have numeric := numeric282 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81))
  rw [oldBefore103, at103, literal, oldAfter282, gammaAfter282]
  exact numeric
theorem numeric283 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 103 p
  rw [at103] at beforeRange
  have afterRange := bonus_range 125 (HazardPattern.afterPattern 10000 p (.walk 125))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ∧ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ≤ 2 at afterRange
  rw [gammaAfter283] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local283 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 125) + NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) + bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 125) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 103 p at decreasing
  rw [gammaAfter283, at103] at decreasing
  have numeric := numeric283 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125))
  rw [oldBefore103, at103, literal, oldAfter283, gammaAfter283]
  exact numeric
theorem numeric284 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 103 p
  rw [at103] at beforeRange
  have afterRange := bonus_range 125 (HazardPattern.afterPattern 10000 p (.push 125 (.stay 147)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 125 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 147))) ∧ bonus (HazardPattern.nextHero (.push 125 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 147))) ≤ 2 at afterRange
  rw [gammaAfter284] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4375 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4375 p complete
    omega
theorem local284 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 125 (HazardPattern.afterPattern 10000 p (.push 125 (.stay 147))) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 125 (.stay 147)) + NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 125 (.stay 147)))) + bonus 125 (HazardPattern.afterPattern 10000 p (.push 125 (.stay 147))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 125 (.stay 147)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 125 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 147))) < bonus 103 p at decreasing
  rw [gammaAfter284, at103] at decreasing
  have numeric := numeric284 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 125 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 147)))
  rw [oldBefore103, at103, literal, oldAfter284, gammaAfter284]
  exact numeric
theorem numeric285 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 103 p
  rw [at103] at beforeRange
  have afterRange := bonus_range 104 (HazardPattern.afterPattern 10000 p (.walk 104))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ∧ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ≤ 2 at afterRange
  rw [gammaAfter285] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local285 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 104) + NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 104))) + bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 104) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 103 p at decreasing
  rw [gammaAfter285, at103] at decreasing
  have numeric := numeric285 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104))
  rw [oldBefore103, at103, literal, oldAfter285, gammaAfter285]
  exact numeric
theorem numeric286 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 103 p
  rw [at103] at beforeRange
  have afterRange := bonus_range 104 (HazardPattern.afterPattern 10000 p (.push 104 (.stay 105)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 104 (.stay 105))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 105))) ∧ bonus (HazardPattern.nextHero (.push 104 (.stay 105))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 105))) ≤ 2 at afterRange
  rw [gammaAfter286] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4375 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4375 p complete
    omega
theorem local286 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 104 (HazardPattern.afterPattern 10000 p (.push 104 (.stay 105))) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 104 (.stay 105)) + NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 104 (.stay 105)))) + bonus 104 (HazardPattern.afterPattern 10000 p (.push 104 (.stay 105))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 104 (.stay 105)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 104 (.stay 105))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 105))) < bonus 103 p at decreasing
  rw [gammaAfter286, at103] at decreasing
  have numeric := numeric286 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 104 (.stay 105))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 105)))
  rw [oldBefore103, at103, literal, oldAfter286, gammaAfter286]
  exact numeric
theorem numeric287 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 103 p
  rw [at103] at beforeRange
  have afterRange := bonus_range 102 (HazardPattern.afterPattern 10000 p (.walk 102))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ∧ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ≤ 2 at afterRange
  rw [gammaAfter287] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local287 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 102) + NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 102))) + bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 102) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 103 p at decreasing
  rw [gammaAfter287, at103] at decreasing
  have numeric := numeric287 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102))
  rw [oldBefore103, at103, literal, oldAfter287, gammaAfter287]
  exact numeric
theorem numeric288 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 103 p
  rw [at103] at beforeRange
  have afterRange := bonus_range 102 (HazardPattern.afterPattern 10000 p (.push 102 (.stay 101)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 102 (.stay 101))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 101))) ∧ bonus (HazardPattern.nextHero (.push 102 (.stay 101))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 101))) ≤ 2 at afterRange
  rw [gammaAfter288] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4375 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4375 p complete
    omega
theorem local288 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 102 (HazardPattern.afterPattern 10000 p (.push 102 (.stay 101))) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 102 (.stay 101)) + NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 102 (.stay 101)))) + bonus 102 (HazardPattern.afterPattern 10000 p (.push 102 (.stay 101))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 102 (.stay 101)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 102 (.stay 101))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 101))) < bonus 103 p at decreasing
  rw [gammaAfter288, at103] at decreasing
  have numeric := numeric288 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 102 (.stay 101))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 101)))
  rw [oldBefore103, at103, literal, oldAfter288, gammaAfter288]
  exact numeric
theorem numeric289 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 103 p
  rw [at103] at beforeRange
  have afterRange := bonus_range 82 (HazardPattern.afterPattern 10000 p (.walk 82))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) ∧ bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) ≤ 2 at afterRange
  rw [gammaAfter289] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local289 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 82 (HazardPattern.afterPattern 10000 p (.walk 82)) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 82) + NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 82))) + bonus 82 (HazardPattern.afterPattern 10000 p (.walk 82)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 82) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) < bonus 103 p at decreasing
  rw [gammaAfter289, at103] at decreasing
  have numeric := numeric289 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82))
  rw [oldBefore103, at103, literal, oldAfter289, gammaAfter289]
  exact numeric
theorem numeric290 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 103 p
  rw [at103] at beforeRange
  have afterRange := bonus_range 80 (HazardPattern.afterPattern 10000 p (.walk 80))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) ∧ bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) ≤ 2 at afterRange
  rw [gammaAfter290] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local290 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 80 (HazardPattern.afterPattern 10000 p (.walk 80)) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 80) + NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 80))) + bonus 80 (HazardPattern.afterPattern 10000 p (.walk 80)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 80) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) < bonus 103 p at decreasing
  rw [gammaAfter290, at103] at decreasing
  have numeric := numeric290 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80))
  rw [oldBefore103, at103, literal, oldAfter290, gammaAfter290]
  exact numeric
theorem numeric291 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 103 p
  rw [at103] at beforeRange
  have afterRange := bonus_range 126 (HazardPattern.afterPattern 10000 p (.walk 126))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ∧ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ≤ 2 at afterRange
  rw [gammaAfter291] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local291 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 126) + NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 126))) + bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 126) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 103 p at decreasing
  rw [gammaAfter291, at103] at decreasing
  have numeric := numeric291 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126))
  rw [oldBefore103, at103, literal, oldAfter291, gammaAfter291]
  exact numeric
theorem numeric292 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 103 p
  rw [at103] at beforeRange
  have afterRange := bonus_range 124 (HazardPattern.afterPattern 10000 p (.walk 124))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ∧ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ≤ 2 at afterRange
  rw [gammaAfter292] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local292 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 124) + NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) + bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 124) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 103 p at decreasing
  rw [gammaAfter292, at103] at decreasing
  have numeric := numeric292 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124))
  rw [oldBefore103, at103, literal, oldAfter292, gammaAfter292]
  exact numeric
theorem numeric293 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 104 p
  rw [at104] at beforeRange
  have afterRange := bonus_range 82 (HazardPattern.afterPattern 10000 p (.walk 82))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) ∧ bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) ≤ 2 at afterRange
  rw [gammaAfter293] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local293 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 82 (HazardPattern.afterPattern 10000 p (.walk 82)) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 82) + NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 82))) + bonus 82 (HazardPattern.afterPattern 10000 p (.walk 82)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 82) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) < bonus 104 p at decreasing
  rw [gammaAfter293, at104] at decreasing
  have numeric := numeric293 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82))
  rw [oldBefore104, at104, literal, oldAfter293, gammaAfter293]
  exact numeric
theorem numeric294 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 104 p
  rw [at104] at beforeRange
  have afterRange := bonus_range 126 (HazardPattern.afterPattern 10000 p (.walk 126))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ∧ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ≤ 2 at afterRange
  rw [gammaAfter294] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local294 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 126) + NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 126))) + bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 126) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 104 p at decreasing
  rw [gammaAfter294, at104] at decreasing
  have numeric := numeric294 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126))
  rw [oldBefore104, at104, literal, oldAfter294, gammaAfter294]
  exact numeric
theorem numeric295 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 104 p
  rw [at104] at beforeRange
  have afterRange := bonus_range 126 (HazardPattern.afterPattern 10000 p (.push 126 (.stay 148)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 126 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 148))) ∧ bonus (HazardPattern.nextHero (.push 126 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 148))) ≤ 2 at afterRange
  rw [gammaAfter295] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4375 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4375 p complete
    omega
theorem local295 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 126 (HazardPattern.afterPattern 10000 p (.push 126 (.stay 148))) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 126 (.stay 148)) + NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 126 (.stay 148)))) + bonus 126 (HazardPattern.afterPattern 10000 p (.push 126 (.stay 148))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 126 (.stay 148)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 126 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 148))) < bonus 104 p at decreasing
  rw [gammaAfter295, at104] at decreasing
  have numeric := numeric295 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 126 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 148)))
  rw [oldBefore104, at104, literal, oldAfter295, gammaAfter295]
  exact numeric
theorem numeric296 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 104 p
  rw [at104] at beforeRange
  have afterRange := bonus_range 105 (HazardPattern.afterPattern 10000 p (.walk 105))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ∧ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ≤ 2 at afterRange
  rw [gammaAfter296] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local296 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 105) + NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 105))) + bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 105) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 104 p at decreasing
  rw [gammaAfter296, at104] at decreasing
  have numeric := numeric296 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105))
  rw [oldBefore104, at104, literal, oldAfter296, gammaAfter296]
  exact numeric
theorem numeric297 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 104 p
  rw [at104] at beforeRange
  have afterRange := bonus_range 105 (HazardPattern.afterPattern 10000 p (.push 105 (.stay 106)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 105 (.stay 106))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 106))) ∧ bonus (HazardPattern.nextHero (.push 105 (.stay 106))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 106))) ≤ 2 at afterRange
  rw [gammaAfter297] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4375 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4375 p complete
    omega
theorem local297 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 105 (HazardPattern.afterPattern 10000 p (.push 105 (.stay 106))) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 105 (.stay 106)) + NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 105 (.stay 106)))) + bonus 105 (HazardPattern.afterPattern 10000 p (.push 105 (.stay 106))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 105 (.stay 106)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 105 (.stay 106))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 106))) < bonus 104 p at decreasing
  rw [gammaAfter297, at104] at decreasing
  have numeric := numeric297 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 105 (.stay 106))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 106)))
  rw [oldBefore104, at104, literal, oldAfter297, gammaAfter297]
  exact numeric
theorem numeric298 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 104 p
  rw [at104] at beforeRange
  have afterRange := bonus_range 103 (HazardPattern.afterPattern 10000 p (.walk 103))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ∧ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ≤ 2 at afterRange
  rw [gammaAfter298] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local298 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 103) + NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 103))) + bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 103) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 104 p at decreasing
  rw [gammaAfter298, at104] at decreasing
  have numeric := numeric298 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103))
  rw [oldBefore104, at104, literal, oldAfter298, gammaAfter298]
  exact numeric
theorem numeric299 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 104 p
  rw [at104] at beforeRange
  have afterRange := bonus_range 103 (HazardPattern.afterPattern 10000 p (.push 103 (.stay 102)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 103 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 102))) ∧ bonus (HazardPattern.nextHero (.push 103 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 102))) ≤ 2 at afterRange
  rw [gammaAfter299] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4375 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4375 p complete
    omega
theorem local299 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 103 (HazardPattern.afterPattern 10000 p (.push 103 (.stay 102))) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 103 (.stay 102)) + NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 103 (.stay 102)))) + bonus 103 (HazardPattern.afterPattern 10000 p (.push 103 (.stay 102))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 103 (.stay 102)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 103 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 102))) < bonus 104 p at decreasing
  rw [gammaAfter299, at104] at decreasing
  have numeric := numeric299 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 103 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 102)))
  rw [oldBefore104, at104, literal, oldAfter299, gammaAfter299]
  exact numeric
theorem numeric300 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 104 p
  rw [at104] at beforeRange
  have afterRange := bonus_range 83 (HazardPattern.afterPattern 10000 p (.walk 83))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) ∧ bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) ≤ 2 at afterRange
  rw [gammaAfter300] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local300 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 83 (HazardPattern.afterPattern 10000 p (.walk 83)) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 83) + NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 83))) + bonus 83 (HazardPattern.afterPattern 10000 p (.walk 83)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 83) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) < bonus 104 p at decreasing
  rw [gammaAfter300, at104] at decreasing
  have numeric := numeric300 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83))
  rw [oldBefore104, at104, literal, oldAfter300, gammaAfter300]
  exact numeric
theorem numeric301 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 104 p
  rw [at104] at beforeRange
  have afterRange := bonus_range 81 (HazardPattern.afterPattern 10000 p (.walk 81))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) ∧ bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) ≤ 2 at afterRange
  rw [gammaAfter301] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local301 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 81 (HazardPattern.afterPattern 10000 p (.walk 81)) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 81) + NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 81))) + bonus 81 (HazardPattern.afterPattern 10000 p (.walk 81)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 81) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) < bonus 104 p at decreasing
  rw [gammaAfter301, at104] at decreasing
  have numeric := numeric301 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81))
  rw [oldBefore104, at104, literal, oldAfter301, gammaAfter301]
  exact numeric
theorem numeric302 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 104 p
  rw [at104] at beforeRange
  have afterRange := bonus_range 127 (HazardPattern.afterPattern 10000 p (.walk 127))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ∧ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ≤ 2 at afterRange
  rw [gammaAfter302] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local302 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 127) + NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) + bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 127) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 104 p at decreasing
  rw [gammaAfter302, at104] at decreasing
  have numeric := numeric302 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127))
  rw [oldBefore104, at104, literal, oldAfter302, gammaAfter302]
  exact numeric
theorem numeric303 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 104 p
  rw [at104] at beforeRange
  have afterRange := bonus_range 125 (HazardPattern.afterPattern 10000 p (.walk 125))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ∧ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ≤ 2 at afterRange
  rw [gammaAfter303] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local303 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 125) + NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) + bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 125) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 104 p at decreasing
  rw [gammaAfter303, at104] at decreasing
  have numeric := numeric303 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125))
  rw [oldBefore104, at104, literal, oldAfter303, gammaAfter303]
  exact numeric
theorem numeric304 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 105 p
  rw [at105] at beforeRange
  have afterRange := bonus_range 83 (HazardPattern.afterPattern 10000 p (.walk 83))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) ∧ bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) ≤ 2 at afterRange
  rw [gammaAfter304] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local304 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 83 (HazardPattern.afterPattern 10000 p (.walk 83)) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 83) + NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 83))) + bonus 83 (HazardPattern.afterPattern 10000 p (.walk 83)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 83) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) < bonus 105 p at decreasing
  rw [gammaAfter304, at105] at decreasing
  have numeric := numeric304 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83))
  rw [oldBefore105, at105, literal, oldAfter304, gammaAfter304]
  exact numeric
theorem numeric305 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 105 p
  rw [at105] at beforeRange
  have afterRange := bonus_range 127 (HazardPattern.afterPattern 10000 p (.walk 127))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ∧ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ≤ 2 at afterRange
  rw [gammaAfter305] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local305 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 127) + NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) + bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 127) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 105 p at decreasing
  rw [gammaAfter305, at105] at decreasing
  have numeric := numeric305 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127))
  rw [oldBefore105, at105, literal, oldAfter305, gammaAfter305]
  exact numeric
theorem numeric306 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 105 p
  rw [at105] at beforeRange
  have afterRange := bonus_range 127 (HazardPattern.afterPattern 10000 p (.push 127 (.stay 149)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 127 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 149))) ∧ bonus (HazardPattern.nextHero (.push 127 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 149))) ≤ 2 at afterRange
  rw [gammaAfter306] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4375 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4375 p complete
    omega
theorem local306 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 127 (HazardPattern.afterPattern 10000 p (.push 127 (.stay 149))) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 127 (.stay 149)) + NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 127 (.stay 149)))) + bonus 127 (HazardPattern.afterPattern 10000 p (.push 127 (.stay 149))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 127 (.stay 149)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 127 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 149))) < bonus 105 p at decreasing
  rw [gammaAfter306, at105] at decreasing
  have numeric := numeric306 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 127 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 149)))
  rw [oldBefore105, at105, literal, oldAfter306, gammaAfter306]
  exact numeric
theorem numeric307 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 105 p
  rw [at105] at beforeRange
  have afterRange := bonus_range 106 (HazardPattern.afterPattern 10000 p (.walk 106))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) ∧ bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) ≤ 2 at afterRange
  rw [gammaAfter307] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local307 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 106 (HazardPattern.afterPattern 10000 p (.walk 106)) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 106) + NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 106))) + bonus 106 (HazardPattern.afterPattern 10000 p (.walk 106)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 106) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) < bonus 105 p at decreasing
  rw [gammaAfter307, at105] at decreasing
  have numeric := numeric307 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106))
  rw [oldBefore105, at105, literal, oldAfter307, gammaAfter307]
  exact numeric
theorem numeric308 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 105 p
  rw [at105] at beforeRange
  have afterRange := bonus_range 104 (HazardPattern.afterPattern 10000 p (.walk 104))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ∧ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ≤ 2 at afterRange
  rw [gammaAfter308] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local308 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 104) + NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 104))) + bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 104) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 105 p at decreasing
  rw [gammaAfter308, at105] at decreasing
  have numeric := numeric308 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104))
  rw [oldBefore105, at105, literal, oldAfter308, gammaAfter308]
  exact numeric
theorem numeric309 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 105 p
  rw [at105] at beforeRange
  have afterRange := bonus_range 104 (HazardPattern.afterPattern 10000 p (.push 104 (.stay 103)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 104 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 103))) ∧ bonus (HazardPattern.nextHero (.push 104 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 103))) ≤ 2 at afterRange
  rw [gammaAfter309] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4375 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4375 p complete
    omega
theorem local309 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 104 (HazardPattern.afterPattern 10000 p (.push 104 (.stay 103))) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 104 (.stay 103)) + NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 104 (.stay 103)))) + bonus 104 (HazardPattern.afterPattern 10000 p (.push 104 (.stay 103))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 104 (.stay 103)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 104 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 103))) < bonus 105 p at decreasing
  rw [gammaAfter309, at105] at decreasing
  have numeric := numeric309 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 104 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 103)))
  rw [oldBefore105, at105, literal, oldAfter309, gammaAfter309]
  exact numeric
theorem numeric310 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 105 p
  rw [at105] at beforeRange
  have afterRange := bonus_range 84 (HazardPattern.afterPattern 10000 p (.walk 84))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84)) ∧ bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84)) ≤ 2 at afterRange
  rw [gammaAfter310] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local310 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 84 (HazardPattern.afterPattern 10000 p (.walk 84)) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 84) + NetHack.Sokoban22Refined85.bonus 84 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 84))) + bonus 84 (HazardPattern.afterPattern 10000 p (.walk 84)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 84) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84)) < bonus 105 p at decreasing
  rw [gammaAfter310, at105] at decreasing
  have numeric := numeric310 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84))
  rw [oldBefore105, at105, literal, oldAfter310, gammaAfter310]
  exact numeric
theorem numeric311 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 105 p
  rw [at105] at beforeRange
  have afterRange := bonus_range 82 (HazardPattern.afterPattern 10000 p (.walk 82))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) ∧ bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) ≤ 2 at afterRange
  rw [gammaAfter311] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local311 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 82 (HazardPattern.afterPattern 10000 p (.walk 82)) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 82) + NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 82))) + bonus 82 (HazardPattern.afterPattern 10000 p (.walk 82)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 82) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) < bonus 105 p at decreasing
  rw [gammaAfter311, at105] at decreasing
  have numeric := numeric311 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82))
  rw [oldBefore105, at105, literal, oldAfter311, gammaAfter311]
  exact numeric
theorem numeric312 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 105 p
  rw [at105] at beforeRange
  have afterRange := bonus_range 128 (HazardPattern.afterPattern 10000 p (.walk 128))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) ∧ bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) ≤ 2 at afterRange
  rw [gammaAfter312] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local312 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 128 (HazardPattern.afterPattern 10000 p (.walk 128)) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 128) + NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 128))) + bonus 128 (HazardPattern.afterPattern 10000 p (.walk 128)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 128) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) < bonus 105 p at decreasing
  rw [gammaAfter312, at105] at decreasing
  have numeric := numeric312 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128))
  rw [oldBefore105, at105, literal, oldAfter312, gammaAfter312]
  exact numeric
theorem numeric313 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 105 p
  rw [at105] at beforeRange
  have afterRange := bonus_range 126 (HazardPattern.afterPattern 10000 p (.walk 126))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ∧ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ≤ 2 at afterRange
  rw [gammaAfter313] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local313 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 126) + NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 126))) + bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 126) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 105 p at decreasing
  rw [gammaAfter313, at105] at decreasing
  have numeric := numeric313 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126))
  rw [oldBefore105, at105, literal, oldAfter313, gammaAfter313]
  exact numeric
theorem numeric314 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 106 p
  rw [at106] at beforeRange
  have afterRange := bonus_range 84 (HazardPattern.afterPattern 10000 p (.walk 84))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84)) ∧ bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84)) ≤ 2 at afterRange
  rw [gammaAfter314] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local314 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 84 (HazardPattern.afterPattern 10000 p (.walk 84)) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 84) + NetHack.Sokoban22Refined85.bonus 84 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 84))) + bonus 84 (HazardPattern.afterPattern 10000 p (.walk 84)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 84) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84)) < bonus 106 p at decreasing
  rw [gammaAfter314, at106] at decreasing
  have numeric := numeric314 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84))
  rw [oldBefore106, at106, literal, oldAfter314, gammaAfter314]
  exact numeric
theorem numeric315 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 106 p
  rw [at106] at beforeRange
  have afterRange := bonus_range 128 (HazardPattern.afterPattern 10000 p (.walk 128))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) ∧ bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) ≤ 2 at afterRange
  rw [gammaAfter315] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local315 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 128 (HazardPattern.afterPattern 10000 p (.walk 128)) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 128) + NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 128))) + bonus 128 (HazardPattern.afterPattern 10000 p (.walk 128)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 128) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) < bonus 106 p at decreasing
  rw [gammaAfter315, at106] at decreasing
  have numeric := numeric315 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128))
  rw [oldBefore106, at106, literal, oldAfter315, gammaAfter315]
  exact numeric
theorem numeric316 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 106 p
  rw [at106] at beforeRange
  have afterRange := bonus_range 128 (HazardPattern.afterPattern 10000 p (.push 128 (.stay 150)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 128 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 128 (.stay 150))) ∧ bonus (HazardPattern.nextHero (.push 128 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 128 (.stay 150))) ≤ 2 at afterRange
  rw [gammaAfter316] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4375 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4375 p complete
    omega
theorem local316 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 128 (HazardPattern.afterPattern 10000 p (.push 128 (.stay 150))) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 128 (.stay 150)) + NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 128 (.stay 150)))) + bonus 128 (HazardPattern.afterPattern 10000 p (.push 128 (.stay 150))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 128 (.stay 150)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 128 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 128 (.stay 150))) < bonus 106 p at decreasing
  rw [gammaAfter316, at106] at decreasing
  have numeric := numeric316 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 128 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 128 (.stay 150)))
  rw [oldBefore106, at106, literal, oldAfter316, gammaAfter316]
  exact numeric
theorem numeric317 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 106 p
  rw [at106] at beforeRange
  have afterRange := bonus_range 105 (HazardPattern.afterPattern 10000 p (.walk 105))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ∧ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ≤ 2 at afterRange
  rw [gammaAfter317] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local317 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 105) + NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 105))) + bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 105) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 106 p at decreasing
  rw [gammaAfter317, at106] at decreasing
  have numeric := numeric317 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105))
  rw [oldBefore106, at106, literal, oldAfter317, gammaAfter317]
  exact numeric
theorem numeric318 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 106 p
  rw [at106] at beforeRange
  have afterRange := bonus_range 105 (HazardPattern.afterPattern 10000 p (.push 105 (.stay 104)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 105 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 104))) ∧ bonus (HazardPattern.nextHero (.push 105 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 104))) ≤ 2 at afterRange
  rw [gammaAfter318] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4375 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro769 p beforeEq beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4375 p complete
    omega
theorem local318 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 105 (HazardPattern.afterPattern 10000 p (.push 105 (.stay 104))) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 105 (.stay 104)) + NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 105 (.stay 104)))) + bonus 105 (HazardPattern.afterPattern 10000 p (.push 105 (.stay 104))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 105 (.stay 104)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 105 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 104))) < bonus 106 p at decreasing
  rw [gammaAfter318, at106] at decreasing
  have numeric := numeric318 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 105 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 104)))
  rw [oldBefore106, at106, literal, oldAfter318, gammaAfter318]
  exact numeric
theorem numeric319 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 106 p
  rw [at106] at beforeRange
  have afterRange := bonus_range 83 (HazardPattern.afterPattern 10000 p (.walk 83))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) ∧ bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) ≤ 2 at afterRange
  rw [gammaAfter319] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local319 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 83 (HazardPattern.afterPattern 10000 p (.walk 83)) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 83) + NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 83))) + bonus 83 (HazardPattern.afterPattern 10000 p (.walk 83)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 83) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) < bonus 106 p at decreasing
  rw [gammaAfter319, at106] at decreasing
  have numeric := numeric319 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83))
  rw [oldBefore106, at106, literal, oldAfter319, gammaAfter319]
  exact numeric
theorem numeric320 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 106 p
  rw [at106] at beforeRange
  have afterRange := bonus_range 127 (HazardPattern.afterPattern 10000 p (.walk 127))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ∧ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ≤ 2 at afterRange
  rw [gammaAfter320] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4373 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4374 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro767 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4373 p complete
    omega
theorem local320 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 127) + NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) + bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 127) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 106 p at decreasing
  rw [gammaAfter320, at106] at decreasing
  have numeric := numeric320 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127))
  rw [oldBefore106, at106, literal, oldAfter320, gammaAfter320]
  exact numeric
theorem numeric321 (p : Pattern) (guard : d74075 p = 1) (decreasing : d4334 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d4334 p := by
  have beforeRange := bonus_range 111 p
  rw [at111] at beforeRange
  have afterRange := bonus_range 89 (HazardPattern.afterPattern 10000 p (.walk 89))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89)) ∧ bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89)) ≤ 2 at afterRange
  rw [gammaAfter321] at afterRange
  have possibilities : (d5849 p = 1 ∧ d4334 p = 0) ∨ (d5849 p = 2 ∧ d4334 p = 0) ∨ (d5849 p = 2 ∧ d4334 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro2633 p pair.2
    have combined := andIntro9200 p guard beforeEq
    have complete := andIntro3778 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro2633 p pair.2
    have combined := andIntro6880 p beforeEq guard
    have complete := andIntro3828 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro2682 p pair.2
    have combined := andIntro6880 p beforeEq guard
    have complete := andIntro3877 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local321 (p : Pattern) (guard : d74075 p = 1)
    (decreasing : bonus 89 (HazardPattern.afterPattern 10000 p (.walk 89)) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 89) + NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 89))) + bonus 89 (HazardPattern.afterPattern 10000 p (.walk 89)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 89) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89)) < bonus 111 p at decreasing
  rw [gammaAfter321, at111] at decreasing
  have numeric := numeric321 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89))
  rw [oldBefore111, at111, literal, oldAfter321, gammaAfter321]
  exact numeric
theorem numeric322 (p : Pattern) (guard : d67924 p = 1) (decreasing : d0 p < d5849 p) :
    d47866 p + d5849 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 111 p
  rw [at111] at beforeRange
  have afterRange := bonus_range 89 (HazardPattern.afterPattern 10000 p (.push 89 (.stay 67)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 89 (.stay 67))) (HazardPattern.afterPattern 10000 p (.push 89 (.stay 67))) ∧ bonus (HazardPattern.nextHero (.push 89 (.stay 67))) (HazardPattern.afterPattern 10000 p (.push 89 (.stay 67))) ≤ 2 at afterRange
  rw [gammaAfter322] at afterRange
  have possibilities : (d5849 p = 1 ∧ d0 p = 0) ∨ (d5849 p = 2 ∧ d0 p = 0) ∨ (d5849 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9244 p guard beforeEq
    have complete := andIntro9245 p afterEq combined
    have bound := compare4392 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro4003 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro4003 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2 p complete
    omega
theorem local322 (p : Pattern) (guard : d67924 p = 1)
    (decreasing : bonus 89 (HazardPattern.afterPattern 10000 p (.push 89 (.stay 67))) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 89 (.stay 67)) + NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 89 (.stay 67)))) + bonus 89 (HazardPattern.afterPattern 10000 p (.push 89 (.stay 67))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 89 (.stay 67)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 89 (.stay 67))) (HazardPattern.afterPattern 10000 p (.push 89 (.stay 67))) < bonus 111 p at decreasing
  rw [gammaAfter322, at111] at decreasing
  have numeric := numeric322 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 89 (.stay 67))) (HazardPattern.afterPattern 10000 p (.push 89 (.stay 67)))
  rw [oldBefore111, at111, literal, oldAfter322, gammaAfter322]
  exact numeric
theorem numeric323 (p : Pattern) (guard : d82685 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 111 p
  rw [at111] at beforeRange
  have afterRange := bonus_range 133 (HazardPattern.afterPattern 10000 p (.walk 133))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) ∧ bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) ≤ 2 at afterRange
  rw [gammaAfter323] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro9246 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro9331 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro9331 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local323 (p : Pattern) (guard : d82685 p = 1)
    (decreasing : bonus 133 (HazardPattern.afterPattern 10000 p (.walk 133)) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 133) + NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 133))) + bonus 133 (HazardPattern.afterPattern 10000 p (.walk 133)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 133) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) < bonus 111 p at decreasing
  rw [gammaAfter323, at111] at decreasing
  have numeric := numeric323 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133))
  rw [oldBefore111, at111, literal, oldAfter323, gammaAfter323]
  exact numeric
theorem numeric324 (p : Pattern) (guard : d82690 p = 1) (decreasing : d0 p < d5849 p) :
    d47866 p + d5849 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 111 p
  rw [at111] at beforeRange
  have afterRange := bonus_range 133 (HazardPattern.afterPattern 10000 p (.push 133 (.stay 155)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 133 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 133 (.stay 155))) ∧ bonus (HazardPattern.nextHero (.push 133 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 133 (.stay 155))) ≤ 2 at afterRange
  rw [gammaAfter324] at afterRange
  have possibilities : (d5849 p = 1 ∧ d0 p = 0) ∨ (d5849 p = 2 ∧ d0 p = 0) ∨ (d5849 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9335 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9339 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9339 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2 p complete
    omega
theorem local324 (p : Pattern) (guard : d82690 p = 1)
    (decreasing : bonus 133 (HazardPattern.afterPattern 10000 p (.push 133 (.stay 155))) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 133 (.stay 155)) + NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 133 (.stay 155)))) + bonus 133 (HazardPattern.afterPattern 10000 p (.push 133 (.stay 155))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 133 (.stay 155)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 133 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 133 (.stay 155))) < bonus 111 p at decreasing
  rw [gammaAfter324, at111] at decreasing
  have numeric := numeric324 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 133 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 133 (.stay 155)))
  rw [oldBefore111, at111, literal, oldAfter324, gammaAfter324]
  exact numeric
theorem numeric325 (p : Pattern) (guard : d77113 p = 1) (decreasing : d4650 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d4650 p := by
  have beforeRange := bonus_range 111 p
  rw [at111] at beforeRange
  have afterRange := bonus_range 90 (HazardPattern.afterPattern 10000 p (.walk 90))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) ∧ bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) ≤ 2 at afterRange
  rw [gammaAfter325] at afterRange
  have possibilities : (d5849 p = 1 ∧ d4650 p = 0) ∨ (d5849 p = 2 ∧ d4650 p = 0) ∨ (d5849 p = 2 ∧ d4650 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro2731 p pair.2
    have combined := andIntro9383 p beforeEq guard
    have complete := andIntro4139 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro2731 p pair.2
    have combined := andIntro9386 p beforeEq guard
    have complete := andIntro4173 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro2732 p pair.2
    have combined := andIntro9386 p beforeEq guard
    have complete := andIntro4174 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local325 (p : Pattern) (guard : d77113 p = 1)
    (decreasing : bonus 90 (HazardPattern.afterPattern 10000 p (.walk 90)) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 90) + NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 90))) + bonus 90 (HazardPattern.afterPattern 10000 p (.walk 90)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 90) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) < bonus 111 p at decreasing
  rw [gammaAfter325, at111] at decreasing
  have numeric := numeric325 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90))
  rw [oldBefore111, at111, literal, oldAfter325, gammaAfter325]
  exact numeric
theorem numeric326 (p : Pattern) (guard : d82694 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 111 p
  rw [at111] at beforeRange
  have afterRange := bonus_range 134 (HazardPattern.afterPattern 10000 p (.walk 134))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ∧ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ≤ 2 at afterRange
  rw [gammaAfter326] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro9387 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro9388 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro9388 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local326 (p : Pattern) (guard : d82694 p = 1)
    (decreasing : bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 134) + NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 134))) + bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 134) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 111 p at decreasing
  rw [gammaAfter326, at111] at decreasing
  have numeric := numeric326 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134))
  rw [oldBefore111, at111, literal, oldAfter326, gammaAfter326]
  exact numeric
theorem numeric327 (p : Pattern) (guard : d75629 p = 1) (decreasing : d5349 p < d6737 p) :
    d47866 p + d6737 p ≤ (0 : Int) + d47866 p + d5349 p := by
  have beforeRange := bonus_range 113 p
  rw [at113] at beforeRange
  have afterRange := bonus_range 91 (HazardPattern.afterPattern 10000 p (.walk 91))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) ∧ bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) ≤ 2 at afterRange
  rw [gammaAfter327] at afterRange
  have possibilities : (d6737 p = 1 ∧ d5349 p = 0) ∨ (d6737 p = 2 ∧ d5349 p = 0) ∨ (d6737 p = 2 ∧ d5349 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3797 p pair.1
    have afterEq := eqIntro2844 p pair.2
    have combined := andIntro9455 p guard beforeEq
    have complete := andIntro9540 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro2844 p pair.2
    have combined := andIntro9572 p guard beforeEq
    have complete := andIntro9616 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro2893 p pair.2
    have combined := andIntro9572 p guard beforeEq
    have complete := andIntro9660 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local327 (p : Pattern) (guard : d75629 p = 1)
    (decreasing : bonus 91 (HazardPattern.afterPattern 10000 p (.walk 91)) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 91) + NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 91))) + bonus 91 (HazardPattern.afterPattern 10000 p (.walk 91)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 91) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) < bonus 113 p at decreasing
  rw [gammaAfter327, at113] at decreasing
  have numeric := numeric327 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91))
  rw [oldBefore113, at113, literal, oldAfter327, gammaAfter327]
  exact numeric
theorem numeric328 (p : Pattern) (guard : d70148 p = 1) (decreasing : d83150 p < d6737 p) :
    d47866 p + d6737 p ≤ (1 : Int) + d47866 p + d83150 p := by
  have beforeRange := bonus_range 113 p
  rw [at113] at beforeRange
  have afterRange := bonus_range 91 (HazardPattern.afterPattern 10000 p (.push 91 (.stay 69)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 91 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 91 (.stay 69))) ∧ bonus (HazardPattern.nextHero (.push 91 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 91 (.stay 69))) ≤ 2 at afterRange
  rw [gammaAfter328] at afterRange
  have possibilities : (d6737 p = 1 ∧ d83150 p = 0) ∨ (d6737 p = 2 ∧ d83150 p = 0) ∨ (d6737 p = 2 ∧ d83150 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3797 p pair.1
    have afterEq := eqIntro4647 p pair.2
    have combined := andIntro9721 p guard beforeEq
    have complete := andIntro9722 p afterEq combined
    have bound := compare4393 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro4647 p pair.2
    have combined := andIntro9754 p guard beforeEq
    have complete := andIntro9798 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro4648 p pair.2
    have combined := andIntro9754 p guard beforeEq
    have complete := andIntro9799 p combined afterEq
    have bound := compare4394 p complete
    omega
theorem local328 (p : Pattern) (guard : d70148 p = 1)
    (decreasing : bonus 91 (HazardPattern.afterPattern 10000 p (.push 91 (.stay 69))) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 91 (.stay 69)) + NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 91 (.stay 69)))) + bonus 91 (HazardPattern.afterPattern 10000 p (.push 91 (.stay 69))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 91 (.stay 69)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 91 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 91 (.stay 69))) < bonus 113 p at decreasing
  rw [gammaAfter328, at113] at decreasing
  have numeric := numeric328 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 91 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 91 (.stay 69)))
  rw [oldBefore113, at113, literal, oldAfter328, gammaAfter328]
  exact numeric
theorem numeric329 (p : Pattern) (guard : d83662 p = 1) (decreasing : d8234 p < d6737 p) :
    d47866 p + d6737 p ≤ (0 : Int) + d47866 p + d8234 p := by
  have beforeRange := bonus_range 113 p
  rw [at113] at beforeRange
  have afterRange := bonus_range 135 (HazardPattern.afterPattern 10000 p (.walk 135))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ∧ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ≤ 2 at afterRange
  rw [gammaAfter329] at afterRange
  have possibilities : (d6737 p = 1 ∧ d8234 p = 0) ∨ (d6737 p = 2 ∧ d8234 p = 0) ∨ (d6737 p = 2 ∧ d8234 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3797 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro9963 p beforeEq guard
    have complete := andIntro10130 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro10162 p beforeEq guard
    have complete := andIntro10211 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro4924 p pair.2
    have combined := andIntro10162 p beforeEq guard
    have complete := andIntro10260 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local329 (p : Pattern) (guard : d83662 p = 1)
    (decreasing : bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 135) + NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 135))) + bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 135) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 113 p at decreasing
  rw [gammaAfter329, at113] at decreasing
  have numeric := numeric329 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135))
  rw [oldBefore113, at113, literal, oldAfter329, gammaAfter329]
  exact numeric
theorem numeric330 (p : Pattern) (guard : d85724 p = 1) (decreasing : d87043 p < d6737 p) :
    d47866 p + d6737 p ≤ (0 : Int) + d47866 p + d87043 p := by
  have beforeRange := bonus_range 113 p
  rw [at113] at beforeRange
  have afterRange := bonus_range 135 (HazardPattern.afterPattern 10000 p (.push 135 (.stay 157)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 135 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 157))) ∧ bonus (HazardPattern.nextHero (.push 135 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 157))) ≤ 2 at afterRange
  rw [gammaAfter330] at afterRange
  have possibilities : (d6737 p = 1 ∧ d87043 p = 0) ∨ (d6737 p = 2 ∧ d87043 p = 0) ∨ (d6737 p = 2 ∧ d87043 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3797 p pair.1
    have afterEq := eqIntro5185 p pair.2
    have combined := andIntro10515 p beforeEq guard
    have complete := andIntro10711 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro5185 p pair.2
    have combined := andIntro10744 p beforeEq guard
    have complete := andIntro10793 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro5279 p pair.2
    have combined := andIntro10744 p beforeEq guard
    have complete := andIntro10837 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local330 (p : Pattern) (guard : d85724 p = 1)
    (decreasing : bonus 135 (HazardPattern.afterPattern 10000 p (.push 135 (.stay 157))) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 135 (.stay 157)) + NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 135 (.stay 157)))) + bonus 135 (HazardPattern.afterPattern 10000 p (.push 135 (.stay 157))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 135 (.stay 157)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 135 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 157))) < bonus 113 p at decreasing
  rw [gammaAfter330, at113] at decreasing
  have numeric := numeric330 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 135 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 157)))
  rw [oldBefore113, at113, literal, oldAfter330, gammaAfter330]
  exact numeric
theorem numeric331 (p : Pattern) (guard : d89600 p = 1) (decreasing : d7239 p < d6737 p) :
    d47866 p + d6737 p ≤ (0 : Int) + d47866 p + d7239 p := by
  have beforeRange := bonus_range 113 p
  rw [at113] at beforeRange
  have afterRange := bonus_range 114 (HazardPattern.afterPattern 10000 p (.walk 114))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) ∧ bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) ≤ 2 at afterRange
  rw [gammaAfter331] at afterRange
  have possibilities : (d6737 p = 1 ∧ d7239 p = 0) ∨ (d6737 p = 2 ∧ d7239 p = 0) ∨ (d6737 p = 2 ∧ d7239 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3797 p pair.1
    have afterEq := eqIntro4312 p pair.2
    have combined := andIntro10838 p beforeEq guard
    have complete := andIntro10928 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro4312 p pair.2
    have combined := andIntro10929 p beforeEq guard
    have complete := andIntro10973 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro4356 p pair.2
    have combined := andIntro10929 p beforeEq guard
    have complete := andIntro11017 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local331 (p : Pattern) (guard : d89600 p = 1)
    (decreasing : bonus 114 (HazardPattern.afterPattern 10000 p (.walk 114)) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 114) + NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 114))) + bonus 114 (HazardPattern.afterPattern 10000 p (.walk 114)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 114) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) < bonus 113 p at decreasing
  rw [gammaAfter331, at113] at decreasing
  have numeric := numeric331 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114))
  rw [oldBefore113, at113, literal, oldAfter331, gammaAfter331]
  exact numeric
theorem numeric332 (p : Pattern) (guard : d89603 p = 1) (decreasing : d90845 p < d6737 p) :
    d47866 p + d6737 p ≤ (0 : Int) + d89607 p + d90845 p := by
  have beforeRange := bonus_range 113 p
  rw [at113] at beforeRange
  have afterRange := bonus_range 114 (HazardPattern.afterPattern 10000 p (.push 114 (.stay 115)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 114 (.stay 115))) (HazardPattern.afterPattern 10000 p (.push 114 (.stay 115))) ∧ bonus (HazardPattern.nextHero (.push 114 (.stay 115))) (HazardPattern.afterPattern 10000 p (.push 114 (.stay 115))) ≤ 2 at afterRange
  rw [gammaAfter332] at afterRange
  have possibilities : (d6737 p = 1 ∧ d90845 p = 0) ∨ (d6737 p = 2 ∧ d90845 p = 0) ∨ (d6737 p = 2 ∧ d90845 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3797 p pair.1
    have afterEq := eqIntro5537 p pair.2
    have combined := andIntro11020 p beforeEq guard
    have complete := andIntro11021 p combined afterEq
    have bound := compare4395 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro5537 p pair.2
    have combined := andIntro11024 p beforeEq guard
    have complete := andIntro11021 p combined afterEq
    have bound := compare4396 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro5622 p pair.2
    have combined := andIntro11024 p beforeEq guard
    have complete := andIntro11025 p combined afterEq
    have bound := compare4395 p complete
    omega
theorem local332 (p : Pattern) (guard : d89603 p = 1)
    (decreasing : bonus 114 (HazardPattern.afterPattern 10000 p (.push 114 (.stay 115))) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 114 (.stay 115)) + NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 114 (.stay 115)))) + bonus 114 (HazardPattern.afterPattern 10000 p (.push 114 (.stay 115))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 114 (.stay 115)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 114 (.stay 115))) (HazardPattern.afterPattern 10000 p (.push 114 (.stay 115))) < bonus 113 p at decreasing
  rw [gammaAfter332, at113] at decreasing
  have numeric := numeric332 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 114 (.stay 115))) (HazardPattern.afterPattern 10000 p (.push 114 (.stay 115)))
  rw [oldBefore113, at113, literal, oldAfter332, gammaAfter332]
  exact numeric
theorem numeric333 (p : Pattern) (guard : d75630 p = 1) (decreasing : d4650 p < d6737 p) :
    d47866 p + d6737 p ≤ (0 : Int) + d47866 p + d4650 p := by
  have beforeRange := bonus_range 113 p
  rw [at113] at beforeRange
  have afterRange := bonus_range 90 (HazardPattern.afterPattern 10000 p (.walk 90))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) ∧ bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) ≤ 2 at afterRange
  rw [gammaAfter333] at afterRange
  have possibilities : (d6737 p = 1 ∧ d4650 p = 0) ∨ (d6737 p = 2 ∧ d4650 p = 0) ∨ (d6737 p = 2 ∧ d4650 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3797 p pair.1
    have afterEq := eqIntro2731 p pair.2
    have combined := andIntro11112 p guard beforeEq
    have complete := andIntro11161 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro2731 p pair.2
    have combined := andIntro11194 p guard beforeEq
    have complete := andIntro4173 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro2732 p pair.2
    have combined := andIntro11194 p guard beforeEq
    have complete := andIntro4174 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local333 (p : Pattern) (guard : d75630 p = 1)
    (decreasing : bonus 90 (HazardPattern.afterPattern 10000 p (.walk 90)) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 90) + NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 90))) + bonus 90 (HazardPattern.afterPattern 10000 p (.walk 90)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 90) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) < bonus 113 p at decreasing
  rw [gammaAfter333, at113] at decreasing
  have numeric := numeric333 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90))
  rw [oldBefore113, at113, literal, oldAfter333, gammaAfter333]
  exact numeric
theorem numeric334 (p : Pattern) (guard : d92317 p = 1) (decreasing : d9291 p < d6737 p) :
    d47866 p + d6737 p ≤ (0 : Int) + d47866 p + d9291 p := by
  have beforeRange := bonus_range 113 p
  rw [at113] at beforeRange
  have afterRange := bonus_range 136 (HazardPattern.afterPattern 10000 p (.walk 136))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ∧ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ≤ 2 at afterRange
  rw [gammaAfter334] at afterRange
  have possibilities : (d6737 p = 1 ∧ d9291 p = 0) ∨ (d6737 p = 2 ∧ d9291 p = 0) ∨ (d6737 p = 2 ∧ d9291 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3797 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro11370 p beforeEq guard
    have complete := andIntro11557 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro11589 p beforeEq guard
    have complete := andIntro11643 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro5906 p pair.2
    have combined := andIntro11589 p beforeEq guard
    have complete := andIntro11692 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local334 (p : Pattern) (guard : d92317 p = 1)
    (decreasing : bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 136) + NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 136))) + bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 136) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 113 p at decreasing
  rw [gammaAfter334, at113] at decreasing
  have numeric := numeric334 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136))
  rw [oldBefore113, at113, literal, oldAfter334, gammaAfter334]
  exact numeric
theorem numeric335 (p : Pattern) (guard : d94517 p = 1) (decreasing : d5849 p < d6737 p) :
    d47866 p + d6737 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 113 p
  rw [at113] at beforeRange
  have afterRange := bonus_range 134 (HazardPattern.afterPattern 10000 p (.walk 134))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ∧ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ≤ 2 at afterRange
  rw [gammaAfter335] at afterRange
  have possibilities : (d6737 p = 1 ∧ d5849 p = 0) ∨ (d6737 p = 2 ∧ d5849 p = 0) ∨ (d6737 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3797 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro11696 p beforeEq guard
    have complete := andIntro11873 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro11877 p beforeEq guard
    have complete := andIntro11921 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4607 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro11877 p beforeEq guard
    have complete := andIntro11965 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local335 (p : Pattern) (guard : d94517 p = 1)
    (decreasing : bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 134) + NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 134))) + bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 134) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 113 p at decreasing
  rw [gammaAfter335, at113] at decreasing
  have numeric := numeric335 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134))
  rw [oldBefore113, at113, literal, oldAfter335, gammaAfter335]
  exact numeric
theorem numeric336 (p : Pattern) (guard : d94518 p = 1) (decreasing : d9291 p < d7239 p) :
    d47866 p + d7239 p ≤ (0 : Int) + d47866 p + d9291 p := by
  have beforeRange := bonus_range 114 p
  rw [at114] at beforeRange
  have afterRange := bonus_range 136 (HazardPattern.afterPattern 10000 p (.walk 136))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ∧ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ≤ 2 at afterRange
  rw [gammaAfter336] at afterRange
  have possibilities : (d7239 p = 1 ∧ d9291 p = 0) ∨ (d7239 p = 2 ∧ d9291 p = 0) ∨ (d7239 p = 2 ∧ d9291 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4356 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro12120 p beforeEq guard
    have complete := andIntro12257 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro12294 p beforeEq guard
    have complete := andIntro12343 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro5906 p pair.2
    have combined := andIntro12294 p beforeEq guard
    have complete := andIntro12387 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local336 (p : Pattern) (guard : d94518 p = 1)
    (decreasing : bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 136) + NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 136))) + bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 136) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 114 p at decreasing
  rw [gammaAfter336, at114] at decreasing
  have numeric := numeric336 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136))
  rw [oldBefore114, at114, literal, oldAfter336, gammaAfter336]
  exact numeric
theorem numeric337 (p : Pattern) (guard : d94756 p = 1) (decreasing : d96219 p < d7239 p) :
    d47866 p + d7239 p ≤ (0 : Int) + d47866 p + d96219 p := by
  have beforeRange := bonus_range 114 p
  rw [at114] at beforeRange
  have afterRange := bonus_range 136 (HazardPattern.afterPattern 10000 p (.push 136 (.stay 158)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 136 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 136 (.stay 158))) ∧ bonus (HazardPattern.nextHero (.push 136 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 136 (.stay 158))) ≤ 2 at afterRange
  rw [gammaAfter337] at afterRange
  have possibilities : (d7239 p = 1 ∧ d96219 p = 0) ∨ (d7239 p = 2 ∧ d96219 p = 0) ∨ (d7239 p = 2 ∧ d96219 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4356 p pair.1
    have afterEq := eqIntro6344 p pair.2
    have combined := andIntro12693 p beforeEq guard
    have complete := andIntro12909 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro6344 p pair.2
    have combined := andIntro12947 p beforeEq guard
    have complete := andIntro12996 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro6464 p pair.2
    have combined := andIntro12947 p beforeEq guard
    have complete := andIntro13040 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local337 (p : Pattern) (guard : d94756 p = 1)
    (decreasing : bonus 136 (HazardPattern.afterPattern 10000 p (.push 136 (.stay 158))) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 136 (.stay 158)) + NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 136 (.stay 158)))) + bonus 136 (HazardPattern.afterPattern 10000 p (.push 136 (.stay 158))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 136 (.stay 158)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 136 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 136 (.stay 158))) < bonus 114 p at decreasing
  rw [gammaAfter337, at114] at decreasing
  have numeric := numeric337 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 136 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 136 (.stay 158)))
  rw [oldBefore114, at114, literal, oldAfter337, gammaAfter337]
  exact numeric
theorem numeric338 (p : Pattern) (guard : d98788 p = 1) (decreasing : d0 p < d7239 p) :
    d47866 p + d7239 p ≤ (0 : Int) + d48097 p + d0 p := by
  have beforeRange := bonus_range 114 p
  rw [at114] at beforeRange
  have afterRange := bonus_range 115 (HazardPattern.afterPattern 10000 p (.walk 115))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) ∧ bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) ≤ 2 at afterRange
  rw [gammaAfter338] at afterRange
  have possibilities : (d7239 p = 1 ∧ d0 p = 0) ∨ (d7239 p = 2 ∧ d0 p = 0) ∨ (d7239 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4356 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro13262 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4397 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro13300 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4398 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro13300 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4397 p complete
    omega
theorem local338 (p : Pattern) (guard : d98788 p = 1)
    (decreasing : bonus 115 (HazardPattern.afterPattern 10000 p (.walk 115)) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 115) + NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 115))) + bonus 115 (HazardPattern.afterPattern 10000 p (.walk 115)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 115) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) < bonus 114 p at decreasing
  rw [gammaAfter338, at114] at decreasing
  have numeric := numeric338 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115))
  rw [oldBefore114, at114, literal, oldAfter338, gammaAfter338]
  exact numeric
theorem numeric339 (p : Pattern) (guard : d98791 p = 1) (decreasing : d0 p < d7239 p) :
    d47866 p + d7239 p ≤ (0 : Int) + d98796 p + d0 p := by
  have beforeRange := bonus_range 114 p
  rw [at114] at beforeRange
  have afterRange := bonus_range 115 (HazardPattern.afterPattern 10000 p (.push 115 (.stay 116)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 115 (.stay 116))) (HazardPattern.afterPattern 10000 p (.push 115 (.stay 116))) ∧ bonus (HazardPattern.nextHero (.push 115 (.stay 116))) (HazardPattern.afterPattern 10000 p (.push 115 (.stay 116))) ≤ 2 at afterRange
  rw [gammaAfter339] at afterRange
  have possibilities : (d7239 p = 1 ∧ d0 p = 0) ∨ (d7239 p = 2 ∧ d0 p = 0) ∨ (d7239 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4356 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro13301 p beforeEq guard
    have complete := andIntro13302 p afterEq combined
    have bound := compare7932 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro13303 p beforeEq guard
    have complete := andIntro13304 p afterEq combined
    have bound := compare10039 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro13303 p beforeEq guard
    have complete := andIntro13305 p afterEq combined
    have bound := compare4399 p complete
    omega
theorem local339 (p : Pattern) (guard : d98791 p = 1)
    (decreasing : bonus 115 (HazardPattern.afterPattern 10000 p (.push 115 (.stay 116))) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 115 (.stay 116)) + NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 115 (.stay 116)))) + bonus 115 (HazardPattern.afterPattern 10000 p (.push 115 (.stay 116))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 115 (.stay 116)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 115 (.stay 116))) (HazardPattern.afterPattern 10000 p (.push 115 (.stay 116))) < bonus 114 p at decreasing
  rw [gammaAfter339, at114] at decreasing
  have numeric := numeric339 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 115 (.stay 116))) (HazardPattern.afterPattern 10000 p (.push 115 (.stay 116)))
  rw [oldBefore114, at114, literal, oldAfter339, gammaAfter339]
  exact numeric
theorem numeric340 (p : Pattern) (guard : d89600 p = 1) (decreasing : d6737 p < d7239 p) :
    d47866 p + d7239 p ≤ (0 : Int) + d47866 p + d6737 p := by
  have beforeRange := bonus_range 114 p
  rw [at114] at beforeRange
  have afterRange := bonus_range 113 (HazardPattern.afterPattern 10000 p (.walk 113))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) ∧ bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) ≤ 2 at afterRange
  rw [gammaAfter340] at afterRange
  have possibilities : (d7239 p = 1 ∧ d6737 p = 0) ∨ (d7239 p = 2 ∧ d6737 p = 0) ∨ (d7239 p = 2 ∧ d6737 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4356 p pair.1
    have afterEq := eqIntro3730 p pair.2
    have combined := andIntro13405 p beforeEq guard
    have complete := andIntro13482 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro3730 p pair.2
    have combined := andIntro13514 p beforeEq guard
    have complete := andIntro13558 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro3797 p pair.2
    have combined := andIntro13514 p beforeEq guard
    have complete := andIntro13602 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local340 (p : Pattern) (guard : d89600 p = 1)
    (decreasing : bonus 113 (HazardPattern.afterPattern 10000 p (.walk 113)) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 113) + NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 113))) + bonus 113 (HazardPattern.afterPattern 10000 p (.walk 113)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 113) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) < bonus 114 p at decreasing
  rw [gammaAfter340, at114] at decreasing
  have numeric := numeric340 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113))
  rw [oldBefore114, at114, literal, oldAfter340, gammaAfter340]
  exact numeric
theorem numeric341 (p : Pattern) (guard : d82334 p = 1) (decreasing : d0 p < d7239 p) :
    d47866 p + d7239 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 114 p
  rw [at114] at beforeRange
  have afterRange := bonus_range 93 (HazardPattern.afterPattern 10000 p (.walk 93))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) ∧ bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) ≤ 2 at afterRange
  rw [gammaAfter341] at afterRange
  have possibilities : (d7239 p = 1 ∧ d0 p = 0) ∨ (d7239 p = 2 ∧ d0 p = 0) ∨ (d7239 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4356 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro13824 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4039 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro13862 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4040 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro13862 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4039 p complete
    omega
theorem local341 (p : Pattern) (guard : d82334 p = 1)
    (decreasing : bonus 93 (HazardPattern.afterPattern 10000 p (.walk 93)) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 93) + NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 93))) + bonus 93 (HazardPattern.afterPattern 10000 p (.walk 93)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 93) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) < bonus 114 p at decreasing
  rw [gammaAfter341, at114] at decreasing
  have numeric := numeric341 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93))
  rw [oldBefore114, at114, literal, oldAfter341, gammaAfter341]
  exact numeric
theorem numeric342 (p : Pattern) (guard : d81525 p = 1) (decreasing : d5349 p < d7239 p) :
    d47866 p + d7239 p ≤ (0 : Int) + d47866 p + d5349 p := by
  have beforeRange := bonus_range 114 p
  rw [at114] at beforeRange
  have afterRange := bonus_range 91 (HazardPattern.afterPattern 10000 p (.walk 91))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) ∧ bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) ≤ 2 at afterRange
  rw [gammaAfter342] at afterRange
  have possibilities : (d7239 p = 1 ∧ d5349 p = 0) ∨ (d7239 p = 2 ∧ d5349 p = 0) ∨ (d7239 p = 2 ∧ d5349 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4356 p pair.1
    have afterEq := eqIntro2844 p pair.2
    have combined := andIntro13929 p guard beforeEq
    have complete := andIntro9540 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro2844 p pair.2
    have combined := andIntro13961 p beforeEq guard
    have complete := andIntro9616 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro2893 p pair.2
    have combined := andIntro13961 p beforeEq guard
    have complete := andIntro9660 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local342 (p : Pattern) (guard : d81525 p = 1)
    (decreasing : bonus 91 (HazardPattern.afterPattern 10000 p (.walk 91)) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 91) + NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 91))) + bonus 91 (HazardPattern.afterPattern 10000 p (.walk 91)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 91) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) < bonus 114 p at decreasing
  rw [gammaAfter342, at114] at decreasing
  have numeric := numeric342 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91))
  rw [oldBefore114, at114, literal, oldAfter342, gammaAfter342]
  exact numeric
theorem numeric343 (p : Pattern) (guard : d98801 p = 1) (decreasing : d8234 p < d7239 p) :
    d47866 p + d7239 p ≤ (0 : Int) + d47866 p + d8234 p := by
  have beforeRange := bonus_range 114 p
  rw [at114] at beforeRange
  have afterRange := bonus_range 135 (HazardPattern.afterPattern 10000 p (.walk 135))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ∧ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ≤ 2 at afterRange
  rw [gammaAfter343] at afterRange
  have possibilities : (d7239 p = 1 ∧ d8234 p = 0) ∨ (d7239 p = 2 ∧ d8234 p = 0) ∨ (d7239 p = 2 ∧ d8234 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4356 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro14128 p beforeEq guard
    have complete := andIntro14267 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro14304 p beforeEq guard
    have complete := andIntro14348 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro6000 p pair.1
    have afterEq := eqIntro4924 p pair.2
    have combined := andIntro14304 p beforeEq guard
    have complete := andIntro14392 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local343 (p : Pattern) (guard : d98801 p = 1)
    (decreasing : bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 135) + NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 135))) + bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 135) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 114 p at decreasing
  rw [gammaAfter343, at114] at decreasing
  have numeric := numeric343 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135))
  rw [oldBefore114, at114, literal, oldAfter343, gammaAfter343]
  exact numeric
theorem numeric344 (p : Pattern) (guard : d82320 p = 1) (decreasing : d0 p < d0 p) :
    d48097 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 115 p
  rw [at115] at beforeRange
  have afterRange := bonus_range 93 (HazardPattern.afterPattern 10000 p (.walk 93))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) ∧ bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) ≤ 2 at afterRange
  rw [gammaAfter344] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9126 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10040 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9126 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10041 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9126 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10040 p complete
    omega
theorem local344 (p : Pattern) (guard : d82320 p = 1)
    (decreasing : bonus 93 (HazardPattern.afterPattern 10000 p (.walk 93)) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 93) + NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 93))) + bonus 93 (HazardPattern.afterPattern 10000 p (.walk 93)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 93) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) < bonus 115 p at decreasing
  rw [gammaAfter344, at115] at decreasing
  have numeric := numeric344 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93))
  rw [oldBefore115, at115, literal, oldAfter344, gammaAfter344]
  exact numeric
theorem numeric345 (p : Pattern) (guard : d73777 p = 1) (decreasing : d0 p < d0 p) :
    d48097 p + d0 p ≤ (2 : Int) + d99411 p + d0 p := by
  have beforeRange := bonus_range 115 p
  rw [at115] at beforeRange
  have afterRange := bonus_range 93 (HazardPattern.afterPattern 10000 p (.push 93 (.stay 71)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 93 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 93 (.stay 71))) ∧ bonus (HazardPattern.nextHero (.push 93 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 93 (.stay 71))) ≤ 2 at afterRange
  rw [gammaAfter345] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14393 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10042 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14393 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10043 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14393 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10042 p complete
    omega
theorem local345 (p : Pattern) (guard : d73777 p = 1)
    (decreasing : bonus 93 (HazardPattern.afterPattern 10000 p (.push 93 (.stay 71))) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 93 (.stay 71)) + NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 93 (.stay 71)))) + bonus 93 (HazardPattern.afterPattern 10000 p (.push 93 (.stay 71))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 93 (.stay 71)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 93 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 93 (.stay 71))) < bonus 115 p at decreasing
  rw [gammaAfter345, at115] at decreasing
  have numeric := numeric345 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 93 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 93 (.stay 71)))
  rw [oldBefore115, at115, literal, oldAfter345, gammaAfter345]
  exact numeric
theorem numeric346 (p : Pattern) (guard : d82331 p = 1) (decreasing : d0 p < d0 p) :
    d48097 p + d0 p ≤ (0 : Int) + d48115 p + d0 p := by
  have beforeRange := bonus_range 115 p
  rw [at115] at beforeRange
  have afterRange := bonus_range 116 (HazardPattern.afterPattern 10000 p (.walk 116))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) ∧ bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) ≤ 2 at afterRange
  rw [gammaAfter346] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14394 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10044 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14394 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10045 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14394 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10044 p complete
    omega
theorem local346 (p : Pattern) (guard : d82331 p = 1)
    (decreasing : bonus 116 (HazardPattern.afterPattern 10000 p (.walk 116)) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 116) + NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 116))) + bonus 116 (HazardPattern.afterPattern 10000 p (.walk 116)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 116) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) < bonus 115 p at decreasing
  rw [gammaAfter346, at115] at decreasing
  have numeric := numeric346 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116))
  rw [oldBefore115, at115, literal, oldAfter346, gammaAfter346]
  exact numeric
theorem numeric347 (p : Pattern) (guard : d98788 p = 1) (decreasing : d7239 p < d0 p) :
    d48097 p + d0 p ≤ (0 : Int) + d47866 p + d7239 p := by
  have beforeRange := bonus_range 115 p
  rw [at115] at beforeRange
  have afterRange := bonus_range 114 (HazardPattern.afterPattern 10000 p (.walk 114))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) ∧ bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) ≤ 2 at afterRange
  rw [gammaAfter347] at afterRange
  have possibilities : (d0 p = 1 ∧ d7239 p = 0) ∨ (d0 p = 2 ∧ d7239 p = 0) ∨ (d0 p = 2 ∧ d7239 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro4312 p pair.2
    have combined := andIntro14395 p beforeEq guard
    have complete := andIntro9132 p combined afterEq
    have bound := compare10046 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro4312 p pair.2
    have combined := andIntro14395 p beforeEq guard
    have complete := andIntro9132 p combined afterEq
    have bound := compare10047 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro4356 p pair.2
    have combined := andIntro14395 p beforeEq guard
    have complete := andIntro9133 p combined afterEq
    have bound := compare10046 p complete
    omega
theorem local347 (p : Pattern) (guard : d98788 p = 1)
    (decreasing : bonus 114 (HazardPattern.afterPattern 10000 p (.walk 114)) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 114) + NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 114))) + bonus 114 (HazardPattern.afterPattern 10000 p (.walk 114)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 114) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) < bonus 115 p at decreasing
  rw [gammaAfter347, at115] at decreasing
  have numeric := numeric347 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114))
  rw [oldBefore115, at115, literal, oldAfter347, gammaAfter347]
  exact numeric
theorem numeric348 (p : Pattern) (guard : d89603 p = 1) (decreasing : d100016 p < d0 p) :
    d48097 p + d0 p ≤ (2 : Int) + d47866 p + d100016 p := by
  have beforeRange := bonus_range 115 p
  rw [at115] at beforeRange
  have afterRange := bonus_range 114 (HazardPattern.afterPattern 10000 p (.push 114 (.stay 113)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 114 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 114 (.stay 113))) ∧ bonus (HazardPattern.nextHero (.push 114 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 114 (.stay 113))) ≤ 2 at afterRange
  rw [gammaAfter348] at afterRange
  have possibilities : (d0 p = 1 ∧ d100016 p = 0) ∨ (d0 p = 2 ∧ d100016 p = 0) ∨ (d0 p = 2 ∧ d100016 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro6549 p pair.2
    have combined := andIntro14396 p beforeEq guard
    have complete := andIntro14397 p combined afterEq
    have bound := compare10048 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro6549 p pair.2
    have combined := andIntro14396 p beforeEq guard
    have complete := andIntro14397 p combined afterEq
    have bound := compare10049 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro6593 p pair.2
    have combined := andIntro14396 p beforeEq guard
    have complete := andIntro14398 p combined afterEq
    have bound := compare10048 p complete
    omega
theorem local348 (p : Pattern) (guard : d89603 p = 1)
    (decreasing : bonus 114 (HazardPattern.afterPattern 10000 p (.push 114 (.stay 113))) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 114 (.stay 113)) + NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 114 (.stay 113)))) + bonus 114 (HazardPattern.afterPattern 10000 p (.push 114 (.stay 113))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 114 (.stay 113)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 114 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 114 (.stay 113))) < bonus 115 p at decreasing
  rw [gammaAfter348, at115] at decreasing
  have numeric := numeric348 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 114 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 114 (.stay 113)))
  rw [oldBefore115, at115, literal, oldAfter348, gammaAfter348]
  exact numeric
theorem numeric349 (p : Pattern) (guard : d82355 p = 1) (decreasing : d0 p < d0 p) :
    d48097 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 115 p
  rw [at115] at beforeRange
  have afterRange := bonus_range 94 (HazardPattern.afterPattern 10000 p (.walk 94))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) ∧ bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) ≤ 2 at afterRange
  rw [gammaAfter349] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9139 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10040 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9139 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10041 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9139 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10040 p complete
    omega
theorem local349 (p : Pattern) (guard : d82355 p = 1)
    (decreasing : bonus 94 (HazardPattern.afterPattern 10000 p (.walk 94)) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 94) + NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 94))) + bonus 94 (HazardPattern.afterPattern 10000 p (.walk 94)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 94) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) < bonus 115 p at decreasing
  rw [gammaAfter349, at115] at decreasing
  have numeric := numeric349 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94))
  rw [oldBefore115, at115, literal, oldAfter349, gammaAfter349]
  exact numeric
end NetHack.Soko22Hazard87
