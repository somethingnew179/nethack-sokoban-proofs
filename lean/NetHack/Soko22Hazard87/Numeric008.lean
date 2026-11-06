import NetHack.Soko22Hazard87.Numeric007
import NetHack.Soko22Hazard87.AndIntroBlocks0167
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric560 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 149 p
  rw [at149] at beforeRange
  have afterRange := bonus_range 150 (HazardPattern.afterPattern 10000 p (.walk 150))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) ∧ bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) ≤ 2 at afterRange
  rw [gammaAfter560] at afterRange
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
theorem local560 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 150 (HazardPattern.afterPattern 10000 p (.walk 150)) < bonus 149 p) :
    NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 149 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 150) + NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 150))) + bonus 150 (HazardPattern.afterPattern 10000 p (.walk 150)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 150) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) < bonus 149 p at decreasing
  rw [gammaAfter560, at149] at decreasing
  have numeric := numeric560 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150))
  rw [oldBefore149, at149, literal, oldAfter560, gammaAfter560]
  exact numeric
theorem numeric561 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 149 p
  rw [at149] at beforeRange
  have afterRange := bonus_range 148 (HazardPattern.afterPattern 10000 p (.walk 148))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ∧ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ≤ 2 at afterRange
  rw [gammaAfter561] at afterRange
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
theorem local561 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 149 p) :
    NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 149 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 148) + NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 148))) + bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 148) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 149 p at decreasing
  rw [gammaAfter561, at149] at decreasing
  have numeric := numeric561 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148))
  rw [oldBefore149, at149, literal, oldAfter561, gammaAfter561]
  exact numeric
theorem numeric562 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 149 p
  rw [at149] at beforeRange
  have afterRange := bonus_range 148 (HazardPattern.afterPattern 10000 p (.push 148 (.stay 147)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 148 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 147))) ∧ bonus (HazardPattern.nextHero (.push 148 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 147))) ≤ 2 at afterRange
  rw [gammaAfter562] at afterRange
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
theorem local562 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 148 (HazardPattern.afterPattern 10000 p (.push 148 (.stay 147))) < bonus 149 p) :
    NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 149 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 148 (.stay 147)) + NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 148 (.stay 147)))) + bonus 148 (HazardPattern.afterPattern 10000 p (.push 148 (.stay 147))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 148 (.stay 147)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 148 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 147))) < bonus 149 p at decreasing
  rw [gammaAfter562, at149] at decreasing
  have numeric := numeric562 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 148 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 147)))
  rw [oldBefore149, at149, literal, oldAfter562, gammaAfter562]
  exact numeric
theorem numeric563 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 149 p
  rw [at149] at beforeRange
  have afterRange := bonus_range 128 (HazardPattern.afterPattern 10000 p (.walk 128))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) ∧ bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) ≤ 2 at afterRange
  rw [gammaAfter563] at afterRange
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
theorem local563 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 128 (HazardPattern.afterPattern 10000 p (.walk 128)) < bonus 149 p) :
    NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 149 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 128) + NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 128))) + bonus 128 (HazardPattern.afterPattern 10000 p (.walk 128)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 128) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) < bonus 149 p at decreasing
  rw [gammaAfter563, at149] at decreasing
  have numeric := numeric563 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128))
  rw [oldBefore149, at149, literal, oldAfter563, gammaAfter563]
  exact numeric
theorem numeric564 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 149 p
  rw [at149] at beforeRange
  have afterRange := bonus_range 126 (HazardPattern.afterPattern 10000 p (.walk 126))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ∧ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ≤ 2 at afterRange
  rw [gammaAfter564] at afterRange
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
theorem local564 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 149 p) :
    NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 149 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 126) + NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 126))) + bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 126) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 149 p at decreasing
  rw [gammaAfter564, at149] at decreasing
  have numeric := numeric564 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126))
  rw [oldBefore149, at149, literal, oldAfter564, gammaAfter564]
  exact numeric
theorem numeric565 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 149 p
  rw [at149] at beforeRange
  have afterRange := bonus_range 172 (HazardPattern.afterPattern 10000 p (.walk 172))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) ∧ bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) ≤ 2 at afterRange
  rw [gammaAfter565] at afterRange
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
theorem local565 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 172 (HazardPattern.afterPattern 10000 p (.walk 172)) < bonus 149 p) :
    NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 149 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 172) + NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 172))) + bonus 172 (HazardPattern.afterPattern 10000 p (.walk 172)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 172) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) < bonus 149 p at decreasing
  rw [gammaAfter565, at149] at decreasing
  have numeric := numeric565 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172))
  rw [oldBefore149, at149, literal, oldAfter565, gammaAfter565]
  exact numeric
theorem numeric566 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 149 p
  rw [at149] at beforeRange
  have afterRange := bonus_range 170 (HazardPattern.afterPattern 10000 p (.walk 170))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ∧ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ≤ 2 at afterRange
  rw [gammaAfter566] at afterRange
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
theorem local566 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 149 p) :
    NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 149 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 170) + NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 170))) + bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 170) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 149 p at decreasing
  rw [gammaAfter566, at149] at decreasing
  have numeric := numeric566 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170))
  rw [oldBefore149, at149, literal, oldAfter566, gammaAfter566]
  exact numeric
theorem numeric567 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 150 p
  rw [at150] at beforeRange
  have afterRange := bonus_range 128 (HazardPattern.afterPattern 10000 p (.walk 128))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) ∧ bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) ≤ 2 at afterRange
  rw [gammaAfter567] at afterRange
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
theorem local567 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 128 (HazardPattern.afterPattern 10000 p (.walk 128)) < bonus 150 p) :
    NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 150 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 128) + NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 128))) + bonus 128 (HazardPattern.afterPattern 10000 p (.walk 128)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 128) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) < bonus 150 p at decreasing
  rw [gammaAfter567, at150] at decreasing
  have numeric := numeric567 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128))
  rw [oldBefore150, at150, literal, oldAfter567, gammaAfter567]
  exact numeric
theorem numeric568 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 150 p
  rw [at150] at beforeRange
  have afterRange := bonus_range 128 (HazardPattern.afterPattern 10000 p (.push 128 (.stay 106)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 128 (.stay 106))) (HazardPattern.afterPattern 10000 p (.push 128 (.stay 106))) ∧ bonus (HazardPattern.nextHero (.push 128 (.stay 106))) (HazardPattern.afterPattern 10000 p (.push 128 (.stay 106))) ≤ 2 at afterRange
  rw [gammaAfter568] at afterRange
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
theorem local568 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 128 (HazardPattern.afterPattern 10000 p (.push 128 (.stay 106))) < bonus 150 p) :
    NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 150 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 128 (.stay 106)) + NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 128 (.stay 106)))) + bonus 128 (HazardPattern.afterPattern 10000 p (.push 128 (.stay 106))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 128 (.stay 106)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 128 (.stay 106))) (HazardPattern.afterPattern 10000 p (.push 128 (.stay 106))) < bonus 150 p at decreasing
  rw [gammaAfter568, at150] at decreasing
  have numeric := numeric568 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 128 (.stay 106))) (HazardPattern.afterPattern 10000 p (.push 128 (.stay 106)))
  rw [oldBefore150, at150, literal, oldAfter568, gammaAfter568]
  exact numeric
theorem numeric569 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 150 p
  rw [at150] at beforeRange
  have afterRange := bonus_range 172 (HazardPattern.afterPattern 10000 p (.walk 172))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) ∧ bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) ≤ 2 at afterRange
  rw [gammaAfter569] at afterRange
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
theorem local569 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 172 (HazardPattern.afterPattern 10000 p (.walk 172)) < bonus 150 p) :
    NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 150 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 172) + NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 172))) + bonus 172 (HazardPattern.afterPattern 10000 p (.walk 172)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 172) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) < bonus 150 p at decreasing
  rw [gammaAfter569, at150] at decreasing
  have numeric := numeric569 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172))
  rw [oldBefore150, at150, literal, oldAfter569, gammaAfter569]
  exact numeric
theorem numeric570 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 150 p
  rw [at150] at beforeRange
  have afterRange := bonus_range 172 (HazardPattern.afterPattern 10000 p (.push 172 (.stay 194)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 172 (.stay 194))) (HazardPattern.afterPattern 10000 p (.push 172 (.stay 194))) ∧ bonus (HazardPattern.nextHero (.push 172 (.stay 194))) (HazardPattern.afterPattern 10000 p (.push 172 (.stay 194))) ≤ 2 at afterRange
  rw [gammaAfter570] at afterRange
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
theorem local570 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 172 (HazardPattern.afterPattern 10000 p (.push 172 (.stay 194))) < bonus 150 p) :
    NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 150 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 172 (.stay 194)) + NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 172 (.stay 194)))) + bonus 172 (HazardPattern.afterPattern 10000 p (.push 172 (.stay 194))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 172 (.stay 194)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 172 (.stay 194))) (HazardPattern.afterPattern 10000 p (.push 172 (.stay 194))) < bonus 150 p at decreasing
  rw [gammaAfter570, at150] at decreasing
  have numeric := numeric570 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 172 (.stay 194))) (HazardPattern.afterPattern 10000 p (.push 172 (.stay 194)))
  rw [oldBefore150, at150, literal, oldAfter570, gammaAfter570]
  exact numeric
theorem numeric571 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 150 p
  rw [at150] at beforeRange
  have afterRange := bonus_range 149 (HazardPattern.afterPattern 10000 p (.walk 149))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ∧ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ≤ 2 at afterRange
  rw [gammaAfter571] at afterRange
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
theorem local571 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 150 p) :
    NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 150 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 149) + NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) + bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 149) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 150 p at decreasing
  rw [gammaAfter571, at150] at decreasing
  have numeric := numeric571 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149))
  rw [oldBefore150, at150, literal, oldAfter571, gammaAfter571]
  exact numeric
theorem numeric572 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 150 p
  rw [at150] at beforeRange
  have afterRange := bonus_range 149 (HazardPattern.afterPattern 10000 p (.push 149 (.stay 148)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 149 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 148))) ∧ bonus (HazardPattern.nextHero (.push 149 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 148))) ≤ 2 at afterRange
  rw [gammaAfter572] at afterRange
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
theorem local572 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 149 (HazardPattern.afterPattern 10000 p (.push 149 (.stay 148))) < bonus 150 p) :
    NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 150 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 149 (.stay 148)) + NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 149 (.stay 148)))) + bonus 149 (HazardPattern.afterPattern 10000 p (.push 149 (.stay 148))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 149 (.stay 148)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 149 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 148))) < bonus 150 p at decreasing
  rw [gammaAfter572, at150] at decreasing
  have numeric := numeric572 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 149 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 148)))
  rw [oldBefore150, at150, literal, oldAfter572, gammaAfter572]
  exact numeric
theorem numeric573 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 150 p
  rw [at150] at beforeRange
  have afterRange := bonus_range 127 (HazardPattern.afterPattern 10000 p (.walk 127))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ∧ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ≤ 2 at afterRange
  rw [gammaAfter573] at afterRange
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
theorem local573 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 150 p) :
    NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 150 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 127) + NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) + bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 127) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 150 p at decreasing
  rw [gammaAfter573, at150] at decreasing
  have numeric := numeric573 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127))
  rw [oldBefore150, at150, literal, oldAfter573, gammaAfter573]
  exact numeric
theorem numeric574 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 150 p
  rw [at150] at beforeRange
  have afterRange := bonus_range 171 (HazardPattern.afterPattern 10000 p (.walk 171))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ∧ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ≤ 2 at afterRange
  rw [gammaAfter574] at afterRange
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
theorem local574 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 150 p) :
    NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 150 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 171) + NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 171))) + bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 171) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 150 p at decreasing
  rw [gammaAfter574, at150] at decreasing
  have numeric := numeric574 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171))
  rw [oldBefore150, at150, literal, oldAfter574, gammaAfter574]
  exact numeric
theorem numeric575 (p : Pattern) (guard : d102593 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 155 p
  rw [at155] at beforeRange
  have afterRange := bonus_range 133 (HazardPattern.afterPattern 10000 p (.walk 133))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) ∧ bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) ≤ 2 at afterRange
  rw [gammaAfter575] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro14420 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro14421 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro14421 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local575 (p : Pattern) (guard : d102593 p = 1)
    (decreasing : bonus 133 (HazardPattern.afterPattern 10000 p (.walk 133)) < bonus 155 p) :
    NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 155 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 133) + NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 133))) + bonus 133 (HazardPattern.afterPattern 10000 p (.walk 133)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 133) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) < bonus 155 p at decreasing
  rw [gammaAfter575, at155] at decreasing
  have numeric := numeric575 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133))
  rw [oldBefore155, at155, literal, oldAfter575, gammaAfter575]
  exact numeric
theorem numeric576 (p : Pattern) (guard : d82690 p = 1) (decreasing : d0 p < d5849 p) :
    d47866 p + d5849 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 155 p
  rw [at155] at beforeRange
  have afterRange := bonus_range 133 (HazardPattern.afterPattern 10000 p (.push 133 (.stay 111)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 133 (.stay 111))) (HazardPattern.afterPattern 10000 p (.push 133 (.stay 111))) ∧ bonus (HazardPattern.nextHero (.push 133 (.stay 111))) (HazardPattern.afterPattern 10000 p (.push 133 (.stay 111))) ≤ 2 at afterRange
  rw [gammaAfter576] at afterRange
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
theorem local576 (p : Pattern) (guard : d82690 p = 1)
    (decreasing : bonus 133 (HazardPattern.afterPattern 10000 p (.push 133 (.stay 111))) < bonus 155 p) :
    NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 155 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 133 (.stay 111)) + NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 133 (.stay 111)))) + bonus 133 (HazardPattern.afterPattern 10000 p (.push 133 (.stay 111))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 133 (.stay 111)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 133 (.stay 111))) (HazardPattern.afterPattern 10000 p (.push 133 (.stay 111))) < bonus 155 p at decreasing
  rw [gammaAfter576, at155] at decreasing
  have numeric := numeric576 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 133 (.stay 111))) (HazardPattern.afterPattern 10000 p (.push 133 (.stay 111)))
  rw [oldBefore155, at155, literal, oldAfter576, gammaAfter576]
  exact numeric
theorem numeric577 (p : Pattern) (guard : d132764 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 155 p
  rw [at155] at beforeRange
  have afterRange := bonus_range 177 (HazardPattern.afterPattern 10000 p (.walk 177))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) ∧ bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) ≤ 2 at afterRange
  rw [gammaAfter577] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro24068 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro24069 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro24069 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local577 (p : Pattern) (guard : d132764 p = 1)
    (decreasing : bonus 177 (HazardPattern.afterPattern 10000 p (.walk 177)) < bonus 155 p) :
    NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 155 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 177) + NetHack.Sokoban22Refined85.bonus 177 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 177))) + bonus 177 (HazardPattern.afterPattern 10000 p (.walk 177)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 177) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) < bonus 155 p at decreasing
  rw [gammaAfter577, at155] at decreasing
  have numeric := numeric577 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177))
  rw [oldBefore155, at155, literal, oldAfter577, gammaAfter577]
  exact numeric
theorem numeric578 (p : Pattern) (guard : d132769 p = 1) (decreasing : d0 p < d5849 p) :
    d47866 p + d5849 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 155 p
  rw [at155] at beforeRange
  have afterRange := bonus_range 177 (HazardPattern.afterPattern 10000 p (.push 177 (.stay 199)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 177 (.stay 199))) (HazardPattern.afterPattern 10000 p (.push 177 (.stay 199))) ∧ bonus (HazardPattern.nextHero (.push 177 (.stay 199))) (HazardPattern.afterPattern 10000 p (.push 177 (.stay 199))) ≤ 2 at afterRange
  rw [gammaAfter578] at afterRange
  have possibilities : (d5849 p = 1 ∧ d0 p = 0) ∨ (d5849 p = 2 ∧ d0 p = 0) ∨ (d5849 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro24073 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro24077 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro24077 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2 p complete
    omega
theorem local578 (p : Pattern) (guard : d132769 p = 1)
    (decreasing : bonus 177 (HazardPattern.afterPattern 10000 p (.push 177 (.stay 199))) < bonus 155 p) :
    NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 155 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 177 (.stay 199)) + NetHack.Sokoban22Refined85.bonus 177 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 177 (.stay 199)))) + bonus 177 (HazardPattern.afterPattern 10000 p (.push 177 (.stay 199))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 177 (.stay 199)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 177 (.stay 199))) (HazardPattern.afterPattern 10000 p (.push 177 (.stay 199))) < bonus 155 p at decreasing
  rw [gammaAfter578, at155] at decreasing
  have numeric := numeric578 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 177 (.stay 199))) (HazardPattern.afterPattern 10000 p (.push 177 (.stay 199)))
  rw [oldBefore155, at155, literal, oldAfter578, gammaAfter578]
  exact numeric
theorem numeric579 (p : Pattern) (guard : d104538 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 155 p
  rw [at155] at beforeRange
  have afterRange := bonus_range 156 (HazardPattern.afterPattern 10000 p (.walk 156))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) ∧ bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) ≤ 2 at afterRange
  rw [gammaAfter579] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro24078 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro24079 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro24079 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local579 (p : Pattern) (guard : d104538 p = 1)
    (decreasing : bonus 156 (HazardPattern.afterPattern 10000 p (.walk 156)) < bonus 155 p) :
    NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 155 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 156) + NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 156))) + bonus 156 (HazardPattern.afterPattern 10000 p (.walk 156)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 156) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) < bonus 155 p at decreasing
  rw [gammaAfter579, at155] at decreasing
  have numeric := numeric579 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156))
  rw [oldBefore155, at155, literal, oldAfter579, gammaAfter579]
  exact numeric
theorem numeric580 (p : Pattern) (guard : d132772 p = 1) (decreasing : d134046 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d134046 p := by
  have beforeRange := bonus_range 155 p
  rw [at155] at beforeRange
  have afterRange := bonus_range 156 (HazardPattern.afterPattern 10000 p (.push 156 (.stay 157)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 156 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 156 (.stay 157))) ∧ bonus (HazardPattern.nextHero (.push 156 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 156 (.stay 157))) ≤ 2 at afterRange
  rw [gammaAfter580] at afterRange
  have possibilities : (d5849 p = 1 ∧ d134046 p = 0) ∨ (d5849 p = 2 ∧ d134046 p = 0) ∨ (d5849 p = 2 ∧ d134046 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro11493 p pair.2
    have combined := andIntro24083 p beforeEq guard
    have complete := andIntro24084 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro11493 p pair.2
    have combined := andIntro24088 p beforeEq guard
    have complete := andIntro24084 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro11587 p pair.2
    have combined := andIntro24088 p beforeEq guard
    have complete := andIntro24089 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local580 (p : Pattern) (guard : d132772 p = 1)
    (decreasing : bonus 156 (HazardPattern.afterPattern 10000 p (.push 156 (.stay 157))) < bonus 155 p) :
    NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 155 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 156 (.stay 157)) + NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 156 (.stay 157)))) + bonus 156 (HazardPattern.afterPattern 10000 p (.push 156 (.stay 157))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 156 (.stay 157)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 156 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 156 (.stay 157))) < bonus 155 p at decreasing
  rw [gammaAfter580, at155] at decreasing
  have numeric := numeric580 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 156 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 156 (.stay 157)))
  rw [oldBefore155, at155, literal, oldAfter580, gammaAfter580]
  exact numeric
theorem numeric581 (p : Pattern) (guard : d109328 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 155 p
  rw [at155] at beforeRange
  have afterRange := bonus_range 134 (HazardPattern.afterPattern 10000 p (.walk 134))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ∧ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ≤ 2 at afterRange
  rw [gammaAfter581] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro16270 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro16271 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro16271 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local581 (p : Pattern) (guard : d109328 p = 1)
    (decreasing : bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 155 p) :
    NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 155 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 134) + NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 134))) + bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 134) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 155 p at decreasing
  rw [gammaAfter581, at155] at decreasing
  have numeric := numeric581 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134))
  rw [oldBefore155, at155, literal, oldAfter581, gammaAfter581]
  exact numeric
theorem numeric582 (p : Pattern) (guard : d104541 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 156 p
  rw [at156] at beforeRange
  have afterRange := bonus_range 134 (HazardPattern.afterPattern 10000 p (.walk 134))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ∧ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ≤ 2 at afterRange
  rw [gammaAfter582] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro14444 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro14445 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro14445 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local582 (p : Pattern) (guard : d104541 p = 1)
    (decreasing : bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 156 p) :
    NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 156 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 134) + NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 134))) + bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 134) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 156 p at decreasing
  rw [gammaAfter582, at156] at decreasing
  have numeric := numeric582 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134))
  rw [oldBefore156, at156, literal, oldAfter582, gammaAfter582]
  exact numeric
theorem numeric583 (p : Pattern) (guard : d135429 p = 1) (decreasing : d12224 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d12224 p := by
  have beforeRange := bonus_range 156 p
  rw [at156] at beforeRange
  have afterRange := bonus_range 157 (HazardPattern.afterPattern 10000 p (.walk 157))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) ∧ bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) ≤ 2 at afterRange
  rw [gammaAfter583] at afterRange
  have possibilities : (d5849 p = 1 ∧ d12224 p = 0) ∨ (d5849 p = 2 ∧ d12224 p = 0) ∨ (d5849 p = 2 ∧ d12224 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro7713 p pair.2
    have combined := andIntro24093 p beforeEq guard
    have complete := andIntro16139 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro7713 p pair.2
    have combined := andIntro24097 p beforeEq guard
    have complete := andIntro16220 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro7817 p pair.2
    have combined := andIntro24097 p beforeEq guard
    have complete := andIntro16269 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local583 (p : Pattern) (guard : d135429 p = 1)
    (decreasing : bonus 157 (HazardPattern.afterPattern 10000 p (.walk 157)) < bonus 156 p) :
    NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 156 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 157) + NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 157))) + bonus 157 (HazardPattern.afterPattern 10000 p (.walk 157)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 157) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) < bonus 156 p at decreasing
  rw [gammaAfter583, at156] at decreasing
  have numeric := numeric583 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157))
  rw [oldBefore156, at156, literal, oldAfter583, gammaAfter583]
  exact numeric
theorem numeric584 (p : Pattern) (guard : d135432 p = 1) (decreasing : d136857 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d136857 p := by
  have beforeRange := bonus_range 156 p
  rw [at156] at beforeRange
  have afterRange := bonus_range 157 (HazardPattern.afterPattern 10000 p (.push 157 (.stay 158)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 157 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 157 (.stay 158))) ∧ bonus (HazardPattern.nextHero (.push 157 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 157 (.stay 158))) ≤ 2 at afterRange
  rw [gammaAfter584] at afterRange
  have possibilities : (d5849 p = 1 ∧ d136857 p = 0) ∨ (d5849 p = 2 ∧ d136857 p = 0) ∨ (d5849 p = 2 ∧ d136857 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro11864 p pair.2
    have combined := andIntro24353 p beforeEq guard
    have complete := andIntro24580 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro11864 p pair.2
    have combined := andIntro24613 p beforeEq guard
    have complete := andIntro24657 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro11958 p pair.2
    have combined := andIntro24613 p beforeEq guard
    have complete := andIntro24701 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local584 (p : Pattern) (guard : d135432 p = 1)
    (decreasing : bonus 157 (HazardPattern.afterPattern 10000 p (.push 157 (.stay 158))) < bonus 156 p) :
    NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 156 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 157 (.stay 158)) + NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 157 (.stay 158)))) + bonus 157 (HazardPattern.afterPattern 10000 p (.push 157 (.stay 158))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 157 (.stay 158)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 157 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 157 (.stay 158))) < bonus 156 p at decreasing
  rw [gammaAfter584, at156] at decreasing
  have numeric := numeric584 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 157 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 157 (.stay 158)))
  rw [oldBefore156, at156, literal, oldAfter584, gammaAfter584]
  exact numeric
theorem numeric585 (p : Pattern) (guard : d104538 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 156 p
  rw [at156] at beforeRange
  have afterRange := bonus_range 155 (HazardPattern.afterPattern 10000 p (.walk 155))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) ∧ bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) ≤ 2 at afterRange
  rw [gammaAfter585] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro24078 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro24079 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro24079 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local585 (p : Pattern) (guard : d104538 p = 1)
    (decreasing : bonus 155 (HazardPattern.afterPattern 10000 p (.walk 155)) < bonus 156 p) :
    NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 156 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 155) + NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 155))) + bonus 155 (HazardPattern.afterPattern 10000 p (.walk 155)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 155) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) < bonus 156 p at decreasing
  rw [gammaAfter585, at156] at decreasing
  have numeric := numeric585 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155))
  rw [oldBefore156, at156, literal, oldAfter585, gammaAfter585]
  exact numeric
theorem numeric586 (p : Pattern) (guard : d115573 p = 1) (decreasing : d8234 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d8234 p := by
  have beforeRange := bonus_range 156 p
  rw [at156] at beforeRange
  have afterRange := bonus_range 135 (HazardPattern.afterPattern 10000 p (.walk 135))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ∧ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ≤ 2 at afterRange
  rw [gammaAfter586] at afterRange
  have possibilities : (d5849 p = 1 ∧ d8234 p = 0) ∨ (d5849 p = 2 ∧ d8234 p = 0) ∨ (d5849 p = 2 ∧ d8234 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro24705 p beforeEq guard
    have complete := andIntro14660 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro24709 p beforeEq guard
    have complete := andIntro14348 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro4924 p pair.2
    have combined := andIntro24709 p beforeEq guard
    have complete := andIntro14392 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local586 (p : Pattern) (guard : d115573 p = 1)
    (decreasing : bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 156 p) :
    NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 156 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 135) + NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 135))) + bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 135) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 156 p at decreasing
  rw [gammaAfter586, at156] at decreasing
  have numeric := numeric586 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135))
  rw [oldBefore156, at156, literal, oldAfter586, gammaAfter586]
  exact numeric
theorem numeric587 (p : Pattern) (guard : d104540 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 156 p
  rw [at156] at beforeRange
  have afterRange := bonus_range 133 (HazardPattern.afterPattern 10000 p (.walk 133))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) ∧ bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) ≤ 2 at afterRange
  rw [gammaAfter587] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro14442 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro14443 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro14443 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local587 (p : Pattern) (guard : d104540 p = 1)
    (decreasing : bonus 133 (HazardPattern.afterPattern 10000 p (.walk 133)) < bonus 156 p) :
    NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 156 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 133) + NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 133))) + bonus 133 (HazardPattern.afterPattern 10000 p (.walk 133)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 133) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) < bonus 156 p at decreasing
  rw [gammaAfter587, at156] at decreasing
  have numeric := numeric587 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133))
  rw [oldBefore156, at156, literal, oldAfter587, gammaAfter587]
  exact numeric
theorem numeric588 (p : Pattern) (guard : d139752 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 156 p
  rw [at156] at beforeRange
  have afterRange := bonus_range 177 (HazardPattern.afterPattern 10000 p (.walk 177))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) ∧ bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) ≤ 2 at afterRange
  rw [gammaAfter588] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro24710 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro24711 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro24711 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local588 (p : Pattern) (guard : d139752 p = 1)
    (decreasing : bonus 177 (HazardPattern.afterPattern 10000 p (.walk 177)) < bonus 156 p) :
    NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 156 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 177) + NetHack.Sokoban22Refined85.bonus 177 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 177))) + bonus 177 (HazardPattern.afterPattern 10000 p (.walk 177)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 177) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) < bonus 156 p at decreasing
  rw [gammaAfter588, at156] at decreasing
  have numeric := numeric588 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177))
  rw [oldBefore156, at156, literal, oldAfter588, gammaAfter588]
  exact numeric
theorem numeric589 (p : Pattern) (guard : d107483 p = 1) (decreasing : d8234 p < d12224 p) :
    d47866 p + d12224 p ≤ (0 : Int) + d47866 p + d8234 p := by
  have beforeRange := bonus_range 157 p
  rw [at157] at beforeRange
  have afterRange := bonus_range 135 (HazardPattern.afterPattern 10000 p (.walk 135))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ∧ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ≤ 2 at afterRange
  rw [gammaAfter589] at afterRange
  have possibilities : (d12224 p = 1 ∧ d8234 p = 0) ∨ (d12224 p = 2 ∧ d8234 p = 0) ∨ (d12224 p = 2 ∧ d8234 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro7817 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro24888 p guard beforeEq
    have complete := andIntro25115 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro25147 p guard beforeEq
    have complete := andIntro25191 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro4924 p pair.2
    have combined := andIntro25147 p guard beforeEq
    have complete := andIntro25235 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local589 (p : Pattern) (guard : d107483 p = 1)
    (decreasing : bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 157 p) :
    NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 157 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 135) + NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 135))) + bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 135) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 157 p at decreasing
  rw [gammaAfter589, at157] at decreasing
  have numeric := numeric589 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135))
  rw [oldBefore157, at157, literal, oldAfter589, gammaAfter589]
  exact numeric
theorem numeric590 (p : Pattern) (guard : d85724 p = 1) (decreasing : d140066 p < d12224 p) :
    d47866 p + d12224 p ≤ (2 : Int) + d47866 p + d140066 p := by
  have beforeRange := bonus_range 157 p
  rw [at157] at beforeRange
  have afterRange := bonus_range 135 (HazardPattern.afterPattern 10000 p (.push 135 (.stay 113)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 135 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 113))) ∧ bonus (HazardPattern.nextHero (.push 135 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 113))) ≤ 2 at afterRange
  rw [gammaAfter590] at afterRange
  have possibilities : (d12224 p = 1 ∧ d140066 p = 0) ∨ (d12224 p = 2 ∧ d140066 p = 0) ∨ (d12224 p = 2 ∧ d140066 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro7817 p pair.1
    have afterEq := eqIntro12299 p pair.2
    have combined := andIntro25472 p guard beforeEq
    have complete := andIntro25623 p afterEq combined
    have bound := compare10984 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro12299 p pair.2
    have combined := andIntro25655 p guard beforeEq
    have complete := andIntro25699 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro12343 p pair.2
    have combined := andIntro25655 p guard beforeEq
    have complete := andIntro25743 p combined afterEq
    have bound := compare10066 p complete
    omega
theorem local590 (p : Pattern) (guard : d85724 p = 1)
    (decreasing : bonus 135 (HazardPattern.afterPattern 10000 p (.push 135 (.stay 113))) < bonus 157 p) :
    NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 157 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 135 (.stay 113)) + NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 135 (.stay 113)))) + bonus 135 (HazardPattern.afterPattern 10000 p (.push 135 (.stay 113))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 135 (.stay 113)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 135 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 113))) < bonus 157 p at decreasing
  rw [gammaAfter590, at157] at decreasing
  have numeric := numeric590 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 135 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 113)))
  rw [oldBefore157, at157, literal, oldAfter590, gammaAfter590]
  exact numeric
theorem numeric591 (p : Pattern) (guard : d112686 p = 1) (decreasing : d13979 p < d12224 p) :
    d47866 p + d12224 p ≤ (0 : Int) + d47866 p + d13979 p := by
  have beforeRange := bonus_range 157 p
  rw [at157] at beforeRange
  have afterRange := bonus_range 158 (HazardPattern.afterPattern 10000 p (.walk 158))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) ∧ bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) ≤ 2 at afterRange
  rw [gammaAfter591] at afterRange
  have possibilities : (d12224 p = 1 ∧ d13979 p = 0) ∨ (d12224 p = 2 ∧ d13979 p = 0) ∨ (d12224 p = 2 ∧ d13979 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro7817 p pair.1
    have afterEq := eqIntro8488 p pair.2
    have combined := andIntro25988 p beforeEq guard
    have complete := andIntro26229 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro8488 p pair.2
    have combined := andIntro26261 p beforeEq guard
    have complete := andIntro26308 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro8624 p pair.2
    have combined := andIntro26261 p beforeEq guard
    have complete := andIntro26352 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local591 (p : Pattern) (guard : d112686 p = 1)
    (decreasing : bonus 158 (HazardPattern.afterPattern 10000 p (.walk 158)) < bonus 157 p) :
    NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 157 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 158) + NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 158))) + bonus 158 (HazardPattern.afterPattern 10000 p (.walk 158)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 158) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) < bonus 157 p at decreasing
  rw [gammaAfter591, at157] at decreasing
  have numeric := numeric591 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158))
  rw [oldBefore157, at157, literal, oldAfter591, gammaAfter591]
  exact numeric
theorem numeric592 (p : Pattern) (guard : d142666 p = 1) (decreasing : d144103 p < d12224 p) :
    d47866 p + d12224 p ≤ (0 : Int) + d47866 p + d144103 p := by
  have beforeRange := bonus_range 157 p
  rw [at157] at beforeRange
  have afterRange := bonus_range 158 (HazardPattern.afterPattern 10000 p (.push 158 (.stay 159)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 158 (.stay 159))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 159))) ∧ bonus (HazardPattern.nextHero (.push 158 (.stay 159))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 159))) ≤ 2 at afterRange
  rw [gammaAfter592] at afterRange
  have possibilities : (d12224 p = 1 ∧ d144103 p = 0) ∨ (d12224 p = 2 ∧ d144103 p = 0) ∨ (d12224 p = 2 ∧ d144103 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro7817 p pair.1
    have afterEq := eqIntro12658 p pair.2
    have combined := andIntro26648 p beforeEq guard
    have complete := andIntro26903 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro12658 p pair.2
    have combined := andIntro26936 p beforeEq guard
    have complete := andIntro26980 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro12772 p pair.2
    have combined := andIntro26936 p beforeEq guard
    have complete := andIntro27024 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local592 (p : Pattern) (guard : d142666 p = 1)
    (decreasing : bonus 158 (HazardPattern.afterPattern 10000 p (.push 158 (.stay 159))) < bonus 157 p) :
    NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 157 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 158 (.stay 159)) + NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 158 (.stay 159)))) + bonus 158 (HazardPattern.afterPattern 10000 p (.push 158 (.stay 159))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 158 (.stay 159)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 158 (.stay 159))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 159))) < bonus 157 p at decreasing
  rw [gammaAfter592, at157] at decreasing
  have numeric := numeric592 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 158 (.stay 159))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 159)))
  rw [oldBefore157, at157, literal, oldAfter592, gammaAfter592]
  exact numeric
theorem numeric593 (p : Pattern) (guard : d135429 p = 1) (decreasing : d5849 p < d12224 p) :
    d47866 p + d12224 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 157 p
  rw [at157] at beforeRange
  have afterRange := bonus_range 156 (HazardPattern.afterPattern 10000 p (.walk 156))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) ∧ bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) ≤ 2 at afterRange
  rw [gammaAfter593] at afterRange
  have possibilities : (d12224 p = 1 ∧ d5849 p = 0) ∨ (d12224 p = 2 ∧ d5849 p = 0) ∨ (d12224 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro7817 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro27025 p beforeEq guard
    have complete := andIntro27202 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro27203 p beforeEq guard
    have complete := andIntro27247 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro27203 p beforeEq guard
    have complete := andIntro27291 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local593 (p : Pattern) (guard : d135429 p = 1)
    (decreasing : bonus 156 (HazardPattern.afterPattern 10000 p (.walk 156)) < bonus 157 p) :
    NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 157 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 156) + NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 156))) + bonus 156 (HazardPattern.afterPattern 10000 p (.walk 156)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 156) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) < bonus 157 p at decreasing
  rw [gammaAfter593, at157] at decreasing
  have numeric := numeric593 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156))
  rw [oldBefore157, at157, literal, oldAfter593, gammaAfter593]
  exact numeric
theorem numeric594 (p : Pattern) (guard : d132772 p = 1) (decreasing : d0 p < d12224 p) :
    d47866 p + d12224 p ≤ (3 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 157 p
  rw [at157] at beforeRange
  have afterRange := bonus_range 156 (HazardPattern.afterPattern 10000 p (.push 156 (.stay 155)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 156 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 156 (.stay 155))) ∧ bonus (HazardPattern.nextHero (.push 156 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 156 (.stay 155))) ≤ 2 at afterRange
  rw [gammaAfter594] at afterRange
  have possibilities : (d12224 p = 1 ∧ d0 p = 0) ∨ (d12224 p = 2 ∧ d0 p = 0) ∨ (d12224 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro7817 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro27295 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10985 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro27299 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10066 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro27299 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10985 p complete
    omega
theorem local594 (p : Pattern) (guard : d132772 p = 1)
    (decreasing : bonus 156 (HazardPattern.afterPattern 10000 p (.push 156 (.stay 155))) < bonus 157 p) :
    NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 157 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 156 (.stay 155)) + NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 156 (.stay 155)))) + bonus 156 (HazardPattern.afterPattern 10000 p (.push 156 (.stay 155))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 156 (.stay 155)) = (3 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 156 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 156 (.stay 155))) < bonus 157 p at decreasing
  rw [gammaAfter594, at157] at decreasing
  have numeric := numeric594 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 156 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 156 (.stay 155)))
  rw [oldBefore157, at157, literal, oldAfter594, gammaAfter594]
  exact numeric
theorem numeric595 (p : Pattern) (guard : d125748 p = 1) (decreasing : d9291 p < d12224 p) :
    d47866 p + d12224 p ≤ (0 : Int) + d47866 p + d9291 p := by
  have beforeRange := bonus_range 157 p
  rw [at157] at beforeRange
  have afterRange := bonus_range 136 (HazardPattern.afterPattern 10000 p (.walk 136))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ∧ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ≤ 2 at afterRange
  rw [gammaAfter595] at afterRange
  have possibilities : (d12224 p = 1 ∧ d9291 p = 0) ∨ (d12224 p = 2 ∧ d9291 p = 0) ∨ (d12224 p = 2 ∧ d9291 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro7817 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro27476 p beforeEq guard
    have complete := andIntro27663 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro27695 p beforeEq guard
    have complete := andIntro27744 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro5906 p pair.2
    have combined := andIntro27695 p beforeEq guard
    have complete := andIntro27788 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local595 (p : Pattern) (guard : d125748 p = 1)
    (decreasing : bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 157 p) :
    NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 157 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 136) + NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 136))) + bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 136) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 157 p at decreasing
  rw [gammaAfter595, at157] at decreasing
  have numeric := numeric595 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136))
  rw [oldBefore157, at157, literal, oldAfter595, gammaAfter595]
  exact numeric
theorem numeric596 (p : Pattern) (guard : d107485 p = 1) (decreasing : d5849 p < d12224 p) :
    d47866 p + d12224 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 157 p
  rw [at157] at beforeRange
  have afterRange := bonus_range 134 (HazardPattern.afterPattern 10000 p (.walk 134))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ∧ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ≤ 2 at afterRange
  rw [gammaAfter596] at afterRange
  have possibilities : (d12224 p = 1 ∧ d5849 p = 0) ∨ (d12224 p = 2 ∧ d5849 p = 0) ∨ (d12224 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro7817 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro27789 p guard beforeEq
    have complete := andIntro27202 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro27790 p guard beforeEq
    have complete := andIntro27247 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro27790 p guard beforeEq
    have complete := andIntro27291 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local596 (p : Pattern) (guard : d107485 p = 1)
    (decreasing : bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 157 p) :
    NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 157 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 134) + NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 134))) + bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 134) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 157 p at decreasing
  rw [gammaAfter596, at157] at decreasing
  have numeric := numeric596 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134))
  rw [oldBefore157, at157, literal, oldAfter596, gammaAfter596]
  exact numeric
theorem numeric597 (p : Pattern) (guard : d146837 p = 1) (decreasing : d23134 p < d12224 p) :
    d47866 p + d12224 p ≤ (0 : Int) + d47866 p + d23134 p := by
  have beforeRange := bonus_range 157 p
  rw [at157] at beforeRange
  have afterRange := bonus_range 180 (HazardPattern.afterPattern 10000 p (.walk 180))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) ∧ bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) ≤ 2 at afterRange
  rw [gammaAfter597] at afterRange
  have possibilities : (d12224 p = 1 ∧ d23134 p = 0) ∨ (d12224 p = 2 ∧ d23134 p = 0) ∨ (d12224 p = 2 ∧ d23134 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro7817 p pair.1
    have afterEq := eqIntro13202 p pair.2
    have combined := andIntro28069 p beforeEq guard
    have complete := andIntro28354 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro13202 p pair.2
    have combined := andIntro28386 p beforeEq guard
    have complete := andIntro28441 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro12250 p pair.1
    have afterEq := eqIntro13358 p pair.2
    have combined := andIntro28386 p beforeEq guard
    have complete := andIntro28490 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local597 (p : Pattern) (guard : d146837 p = 1)
    (decreasing : bonus 180 (HazardPattern.afterPattern 10000 p (.walk 180)) < bonus 157 p) :
    NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 157 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 180) + NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 180))) + bonus 180 (HazardPattern.afterPattern 10000 p (.walk 180)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 180) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) < bonus 157 p at decreasing
  rw [gammaAfter597, at157] at decreasing
  have numeric := numeric597 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180))
  rw [oldBefore157, at157, literal, oldAfter597, gammaAfter597]
  exact numeric
theorem numeric598 (p : Pattern) (guard : d115574 p = 1) (decreasing : d9291 p < d13979 p) :
    d47866 p + d13979 p ≤ (0 : Int) + d47866 p + d9291 p := by
  have beforeRange := bonus_range 158 p
  rw [at158] at beforeRange
  have afterRange := bonus_range 136 (HazardPattern.afterPattern 10000 p (.walk 136))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ∧ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ≤ 2 at afterRange
  rw [gammaAfter598] at afterRange
  have possibilities : (d13979 p = 1 ∧ d9291 p = 0) ∨ (d13979 p = 2 ∧ d9291 p = 0) ∨ (d13979 p = 2 ∧ d9291 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro8624 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro28671 p beforeEq guard
    have complete := andIntro28934 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro28969 p guard beforeEq
    have complete := andIntro29018 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro5906 p pair.2
    have combined := andIntro28969 p guard beforeEq
    have complete := andIntro29062 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local598 (p : Pattern) (guard : d115574 p = 1)
    (decreasing : bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 158 p) :
    NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 158 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 136) + NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 136))) + bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 136) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 158 p at decreasing
  rw [gammaAfter598, at158] at decreasing
  have numeric := numeric598 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136))
  rw [oldBefore158, at158, literal, oldAfter598, gammaAfter598]
  exact numeric
theorem numeric599 (p : Pattern) (guard : d94756 p = 1) (decreasing : d0 p < d13979 p) :
    d47866 p + d13979 p ≤ (2 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 158 p
  rw [at158] at beforeRange
  have afterRange := bonus_range 136 (HazardPattern.afterPattern 10000 p (.push 136 (.stay 114)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 136 (.stay 114))) (HazardPattern.afterPattern 10000 p (.push 136 (.stay 114))) ∧ bonus (HazardPattern.nextHero (.push 136 (.stay 114))) (HazardPattern.afterPattern 10000 p (.push 136 (.stay 114))) ≤ 2 at afterRange
  rw [gammaAfter599] at afterRange
  have possibilities : (d13979 p = 1 ∧ d0 p = 0) ∨ (d13979 p = 2 ∧ d0 p = 0) ∨ (d13979 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro8624 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro29303 p guard beforeEq
    have complete := andIntro29304 p afterEq combined
    have bound := compare10986 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro29339 p guard beforeEq
    have complete := andIntro29340 p afterEq combined
    have bound := compare10987 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro29339 p guard beforeEq
    have complete := andIntro29341 p afterEq combined
    have bound := compare10066 p complete
    omega
theorem local599 (p : Pattern) (guard : d94756 p = 1)
    (decreasing : bonus 136 (HazardPattern.afterPattern 10000 p (.push 136 (.stay 114))) < bonus 158 p) :
    NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 158 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 136 (.stay 114)) + NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 136 (.stay 114)))) + bonus 136 (HazardPattern.afterPattern 10000 p (.push 136 (.stay 114))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 136 (.stay 114)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 136 (.stay 114))) (HazardPattern.afterPattern 10000 p (.push 136 (.stay 114))) < bonus 158 p at decreasing
  rw [gammaAfter599, at158] at decreasing
  have numeric := numeric599 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 136 (.stay 114))) (HazardPattern.afterPattern 10000 p (.push 136 (.stay 114)))
  rw [oldBefore158, at158, literal, oldAfter599, gammaAfter599]
  exact numeric
theorem numeric600 (p : Pattern) (guard : d146836 p = 1) (decreasing : d23134 p < d13979 p) :
    d47866 p + d13979 p ≤ (0 : Int) + d47866 p + d23134 p := by
  have beforeRange := bonus_range 158 p
  rw [at158] at beforeRange
  have afterRange := bonus_range 180 (HazardPattern.afterPattern 10000 p (.walk 180))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) ∧ bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) ≤ 2 at afterRange
  rw [gammaAfter600] at afterRange
  have possibilities : (d13979 p = 1 ∧ d23134 p = 0) ∨ (d13979 p = 2 ∧ d23134 p = 0) ∨ (d13979 p = 2 ∧ d23134 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro8624 p pair.1
    have afterEq := eqIntro13202 p pair.2
    have combined := andIntro29637 p beforeEq guard
    have complete := andIntro29918 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro13202 p pair.2
    have combined := andIntro29953 p guard beforeEq
    have complete := andIntro30003 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro13358 p pair.2
    have combined := andIntro29953 p guard beforeEq
    have complete := andIntro30047 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local600 (p : Pattern) (guard : d146836 p = 1)
    (decreasing : bonus 180 (HazardPattern.afterPattern 10000 p (.walk 180)) < bonus 158 p) :
    NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 158 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 180) + NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 180))) + bonus 180 (HazardPattern.afterPattern 10000 p (.walk 180)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 180) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) < bonus 158 p at decreasing
  rw [gammaAfter600, at158] at decreasing
  have numeric := numeric600 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180))
  rw [oldBefore158, at158, literal, oldAfter600, gammaAfter600]
  exact numeric
theorem numeric601 (p : Pattern) (guard : d152855 p = 1) (decreasing : d154952 p < d13979 p) :
    d47866 p + d13979 p ≤ (0 : Int) + d47866 p + d154952 p := by
  have beforeRange := bonus_range 158 p
  rw [at158] at beforeRange
  have afterRange := bonus_range 180 (HazardPattern.afterPattern 10000 p (.push 180 (.stay 202)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 180 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 180 (.stay 202))) ∧ bonus (HazardPattern.nextHero (.push 180 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 180 (.stay 202))) ≤ 2 at afterRange
  rw [gammaAfter601] at afterRange
  have possibilities : (d13979 p = 1 ∧ d154952 p = 0) ∨ (d13979 p = 2 ∧ d154952 p = 0) ∨ (d13979 p = 2 ∧ d154952 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro8624 p pair.1
    have afterEq := eqIntro14111 p pair.2
    have combined := andIntro30390 p beforeEq guard
    have complete := andIntro30680 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro14111 p pair.2
    have combined := andIntro30716 p beforeEq guard
    have complete := andIntro30763 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro14253 p pair.2
    have combined := andIntro30716 p beforeEq guard
    have complete := andIntro30807 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local601 (p : Pattern) (guard : d152855 p = 1)
    (decreasing : bonus 180 (HazardPattern.afterPattern 10000 p (.push 180 (.stay 202))) < bonus 158 p) :
    NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 158 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 180 (.stay 202)) + NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 180 (.stay 202)))) + bonus 180 (HazardPattern.afterPattern 10000 p (.push 180 (.stay 202))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 180 (.stay 202)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 180 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 180 (.stay 202))) < bonus 158 p at decreasing
  rw [gammaAfter601, at158] at decreasing
  have numeric := numeric601 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 180 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 180 (.stay 202)))
  rw [oldBefore158, at158, literal, oldAfter601, gammaAfter601]
  exact numeric
theorem numeric602 (p : Pattern) (guard : d122305 p = 1) (decreasing : d15965 p < d13979 p) :
    d47866 p + d13979 p ≤ (0 : Int) + d47866 p + d15965 p := by
  have beforeRange := bonus_range 158 p
  rw [at158] at beforeRange
  have afterRange := bonus_range 159 (HazardPattern.afterPattern 10000 p (.walk 159))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ∧ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ≤ 2 at afterRange
  rw [gammaAfter602] at afterRange
  have possibilities : (d13979 p = 1 ∧ d15965 p = 0) ∨ (d13979 p = 2 ∧ d15965 p = 0) ∨ (d13979 p = 2 ∧ d15965 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro8624 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro31076 p beforeEq guard
    have complete := andIntro31270 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro31305 p guard beforeEq
    have complete := andIntro31355 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro9862 p pair.2
    have combined := andIntro31305 p guard beforeEq
    have complete := andIntro31399 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local602 (p : Pattern) (guard : d122305 p = 1)
    (decreasing : bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 158 p) :
    NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 158 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 159) + NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 159))) + bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 159) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 158 p at decreasing
  rw [gammaAfter602, at158] at decreasing
  have numeric := numeric602 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159))
  rw [oldBefore158, at158, literal, oldAfter602, gammaAfter602]
  exact numeric
theorem numeric603 (p : Pattern) (guard : d159762 p = 1) (decreasing : d0 p < d13979 p) :
    d47866 p + d13979 p ≤ (0 : Int) + d159795 p + d0 p := by
  have beforeRange := bonus_range 158 p
  rw [at158] at beforeRange
  have afterRange := bonus_range 159 (HazardPattern.afterPattern 10000 p (.push 159 (.stay 160)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 159 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 159 (.stay 160))) ∧ bonus (HazardPattern.nextHero (.push 159 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 159 (.stay 160))) ≤ 2 at afterRange
  rw [gammaAfter603] at afterRange
  have possibilities : (d13979 p = 1 ∧ d0 p = 0) ∨ (d13979 p = 2 ∧ d0 p = 0) ∨ (d13979 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro8624 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro31713 p beforeEq guard
    have complete := andIntro31714 p afterEq combined
    have bound := compare12783 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro31750 p beforeEq guard
    have complete := andIntro31751 p afterEq combined
    have bound := compare13651 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro31750 p beforeEq guard
    have complete := andIntro31752 p afterEq combined
    have bound := compare10988 p complete
    omega
theorem local603 (p : Pattern) (guard : d159762 p = 1)
    (decreasing : bonus 159 (HazardPattern.afterPattern 10000 p (.push 159 (.stay 160))) < bonus 158 p) :
    NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 158 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 159 (.stay 160)) + NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 159 (.stay 160)))) + bonus 159 (HazardPattern.afterPattern 10000 p (.push 159 (.stay 160))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 159 (.stay 160)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 159 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 159 (.stay 160))) < bonus 158 p at decreasing
  rw [gammaAfter603, at158] at decreasing
  have numeric := numeric603 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 159 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 159 (.stay 160)))
  rw [oldBefore158, at158, literal, oldAfter603, gammaAfter603]
  exact numeric
theorem numeric604 (p : Pattern) (guard : d112686 p = 1) (decreasing : d12224 p < d13979 p) :
    d47866 p + d13979 p ≤ (0 : Int) + d47866 p + d12224 p := by
  have beforeRange := bonus_range 158 p
  rw [at158] at beforeRange
  have afterRange := bonus_range 157 (HazardPattern.afterPattern 10000 p (.walk 157))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) ∧ bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) ≤ 2 at afterRange
  rw [gammaAfter604] at afterRange
  have possibilities : (d13979 p = 1 ∧ d12224 p = 0) ∨ (d13979 p = 2 ∧ d12224 p = 0) ∨ (d13979 p = 2 ∧ d12224 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro8624 p pair.1
    have afterEq := eqIntro7713 p pair.2
    have combined := andIntro31993 p guard beforeEq
    have complete := andIntro32230 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro7713 p pair.2
    have combined := andIntro32265 p guard beforeEq
    have complete := andIntro32309 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro7817 p pair.2
    have combined := andIntro32265 p guard beforeEq
    have complete := andIntro32353 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local604 (p : Pattern) (guard : d112686 p = 1)
    (decreasing : bonus 157 (HazardPattern.afterPattern 10000 p (.walk 157)) < bonus 158 p) :
    NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 158 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 157) + NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 157))) + bonus 157 (HazardPattern.afterPattern 10000 p (.walk 157)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 157) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) < bonus 158 p at decreasing
  rw [gammaAfter604, at158] at decreasing
  have numeric := numeric604 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157))
  rw [oldBefore158, at158, literal, oldAfter604, gammaAfter604]
  exact numeric
theorem numeric605 (p : Pattern) (guard : d135432 p = 1) (decreasing : d0 p < d13979 p) :
    d47866 p + d13979 p ≤ (2 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 158 p
  rw [at158] at beforeRange
  have afterRange := bonus_range 157 (HazardPattern.afterPattern 10000 p (.push 157 (.stay 156)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 157 (.stay 156))) (HazardPattern.afterPattern 10000 p (.push 157 (.stay 156))) ∧ bonus (HazardPattern.nextHero (.push 157 (.stay 156))) (HazardPattern.afterPattern 10000 p (.push 157 (.stay 156))) ≤ 2 at afterRange
  rw [gammaAfter605] at afterRange
  have possibilities : (d13979 p = 1 ∧ d0 p = 0) ∨ (d13979 p = 2 ∧ d0 p = 0) ∨ (d13979 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro8624 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro32594 p beforeEq guard
    have complete := andIntro32595 p afterEq combined
    have bound := compare13652 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro32630 p guard beforeEq
    have complete := andIntro32631 p afterEq combined
    have bound := compare13653 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro32630 p guard beforeEq
    have complete := andIntro32632 p afterEq combined
    have bound := compare10066 p complete
    omega
theorem local605 (p : Pattern) (guard : d135432 p = 1)
    (decreasing : bonus 157 (HazardPattern.afterPattern 10000 p (.push 157 (.stay 156))) < bonus 158 p) :
    NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 158 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 157 (.stay 156)) + NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 157 (.stay 156)))) + bonus 157 (HazardPattern.afterPattern 10000 p (.push 157 (.stay 156))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 157 (.stay 156)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 157 (.stay 156))) (HazardPattern.afterPattern 10000 p (.push 157 (.stay 156))) < bonus 158 p at decreasing
  rw [gammaAfter605, at158] at decreasing
  have numeric := numeric605 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 157 (.stay 156))) (HazardPattern.afterPattern 10000 p (.push 157 (.stay 156)))
  rw [oldBefore158, at158, literal, oldAfter605, gammaAfter605]
  exact numeric
theorem numeric606 (p : Pattern) (guard : d112688 p = 1) (decreasing : d8234 p < d13979 p) :
    d47866 p + d13979 p ≤ (0 : Int) + d47866 p + d8234 p := by
  have beforeRange := bonus_range 158 p
  rw [at158] at beforeRange
  have afterRange := bonus_range 135 (HazardPattern.afterPattern 10000 p (.walk 135))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ∧ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ≤ 2 at afterRange
  rw [gammaAfter606] at afterRange
  have possibilities : (d13979 p = 1 ∧ d8234 p = 0) ∨ (d13979 p = 2 ∧ d8234 p = 0) ∨ (d13979 p = 2 ∧ d8234 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro8624 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro32813 p guard beforeEq
    have complete := andIntro32980 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro33015 p guard beforeEq
    have complete := andIntro33059 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro4924 p pair.2
    have combined := andIntro33015 p guard beforeEq
    have complete := andIntro33103 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local606 (p : Pattern) (guard : d112688 p = 1)
    (decreasing : bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 158 p) :
    NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 158 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 135) + NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 135))) + bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 135) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 158 p at decreasing
  rw [gammaAfter606, at158] at decreasing
  have numeric := numeric606 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135))
  rw [oldBefore158, at158, literal, oldAfter606, gammaAfter606]
  exact numeric
theorem numeric607 (p : Pattern) (guard : d162095 p = 1) (decreasing : d17560 p < d13979 p) :
    d47866 p + d13979 p ≤ (0 : Int) + d47866 p + d17560 p := by
  have beforeRange := bonus_range 158 p
  rw [at158] at beforeRange
  have afterRange := bonus_range 181 (HazardPattern.afterPattern 10000 p (.walk 181))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ∧ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ≤ 2 at afterRange
  rw [gammaAfter607] at afterRange
  have possibilities : (d13979 p = 1 ∧ d17560 p = 0) ∨ (d13979 p = 2 ∧ d17560 p = 0) ∨ (d13979 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro8624 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro33324 p beforeEq guard
    have complete := andIntro33592 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro33623 p beforeEq guard
    have complete := andIntro33673 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro13723 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro33623 p beforeEq guard
    have complete := andIntro33717 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local607 (p : Pattern) (guard : d162095 p = 1)
    (decreasing : bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 158 p) :
    NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 158 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 181) + NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 181))) + bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 181) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 158 p at decreasing
  rw [gammaAfter607, at158] at decreasing
  have numeric := numeric607 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181))
  rw [oldBefore158, at158, literal, oldAfter607, gammaAfter607]
  exact numeric
theorem numeric608 (p : Pattern) (guard : d163444 p = 1) (decreasing : d17560 p < d15965 p) :
    d47866 p + d15965 p ≤ (0 : Int) + d47866 p + d17560 p := by
  have beforeRange := bonus_range 159 p
  rw [at159] at beforeRange
  have afterRange := bonus_range 181 (HazardPattern.afterPattern 10000 p (.walk 181))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ∧ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ≤ 2 at afterRange
  rw [gammaAfter608] at afterRange
  have possibilities : (d15965 p = 1 ∧ d17560 p = 0) ∨ (d15965 p = 2 ∧ d17560 p = 0) ∨ (d15965 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro9862 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro33718 p beforeEq guard
    have complete := andIntro34008 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro34009 p guard beforeEq
    have complete := andIntro34059 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro34009 p guard beforeEq
    have complete := andIntro34103 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local608 (p : Pattern) (guard : d163444 p = 1)
    (decreasing : bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 159 p) :
    NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 159 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 181) + NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 181))) + bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 181) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 159 p at decreasing
  rw [gammaAfter608, at159] at decreasing
  have numeric := numeric608 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181))
  rw [oldBefore159, at159, literal, oldAfter608, gammaAfter608]
  exact numeric
theorem numeric609 (p : Pattern) (guard : d129471 p = 1) (decreasing : d17560 p < d15965 p) :
    d47866 p + d15965 p ≤ (0 : Int) + d48388 p + d17560 p := by
  have beforeRange := bonus_range 159 p
  rw [at159] at beforeRange
  have afterRange := bonus_range 160 (HazardPattern.afterPattern 10000 p (.walk 160))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) ∧ bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) ≤ 2 at afterRange
  rw [gammaAfter609] at afterRange
  have possibilities : (d15965 p = 1 ∧ d17560 p = 0) ∨ (d15965 p = 2 ∧ d17560 p = 0) ∨ (d15965 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro9862 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro34104 p beforeEq guard
    have complete := andIntro34008 p combined afterEq
    have bound := compare13654 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro34105 p guard beforeEq
    have complete := andIntro34059 p afterEq combined
    have bound := compare13655 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro34105 p guard beforeEq
    have complete := andIntro34103 p afterEq combined
    have bound := compare13654 p complete
    omega
theorem local609 (p : Pattern) (guard : d129471 p = 1)
    (decreasing : bonus 160 (HazardPattern.afterPattern 10000 p (.walk 160)) < bonus 159 p) :
    NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 159 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 160) + NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 160))) + bonus 160 (HazardPattern.afterPattern 10000 p (.walk 160)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 160) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) < bonus 159 p at decreasing
  rw [gammaAfter609, at159] at decreasing
  have numeric := numeric609 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160))
  rw [oldBefore159, at159, literal, oldAfter609, gammaAfter609]
  exact numeric
theorem numeric610 (p : Pattern) (guard : d163684 p = 1) (decreasing : d165069 p < d15965 p) :
    d47866 p + d15965 p ≤ (2 : Int) + d163714 p + d165069 p := by
  have beforeRange := bonus_range 159 p
  rw [at159] at beforeRange
  have afterRange := bonus_range 160 (HazardPattern.afterPattern 10000 p (.push 160 (.stay 161)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 160 (.stay 161))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 161))) ∧ bonus (HazardPattern.nextHero (.push 160 (.stay 161))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 161))) ≤ 2 at afterRange
  rw [gammaAfter610] at afterRange
  have possibilities : (d15965 p = 1 ∧ d165069 p = 0) ∨ (d15965 p = 2 ∧ d165069 p = 0) ∨ (d15965 p = 2 ∧ d165069 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro9862 p pair.1
    have afterEq := eqIntro14923 p pair.2
    have combined := andIntro34428 p beforeEq guard
    have complete := andIntro34429 p combined afterEq
    have bound := compare13656 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro14923 p pair.2
    have combined := andIntro34468 p beforeEq guard
    have complete := andIntro34429 p combined afterEq
    have bound := compare13657 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro15019 p pair.2
    have combined := andIntro34468 p beforeEq guard
    have complete := andIntro34469 p combined afterEq
    have bound := compare13656 p complete
    omega
theorem local610 (p : Pattern) (guard : d163684 p = 1)
    (decreasing : bonus 160 (HazardPattern.afterPattern 10000 p (.push 160 (.stay 161))) < bonus 159 p) :
    NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 159 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 160 (.stay 161)) + NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 160 (.stay 161)))) + bonus 160 (HazardPattern.afterPattern 10000 p (.push 160 (.stay 161))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 160 (.stay 161)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 160 (.stay 161))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 161))) < bonus 159 p at decreasing
  rw [gammaAfter610, at159] at decreasing
  have numeric := numeric610 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 160 (.stay 161))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 161)))
  rw [oldBefore159, at159, literal, oldAfter610, gammaAfter610]
  exact numeric
theorem numeric611 (p : Pattern) (guard : d122305 p = 1) (decreasing : d13979 p < d15965 p) :
    d47866 p + d15965 p ≤ (0 : Int) + d47866 p + d13979 p := by
  have beforeRange := bonus_range 159 p
  rw [at159] at beforeRange
  have afterRange := bonus_range 158 (HazardPattern.afterPattern 10000 p (.walk 158))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) ∧ bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) ≤ 2 at afterRange
  rw [gammaAfter611] at afterRange
  have possibilities : (d15965 p = 1 ∧ d13979 p = 0) ∨ (d15965 p = 2 ∧ d13979 p = 0) ∨ (d15965 p = 2 ∧ d13979 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro9862 p pair.1
    have afterEq := eqIntro8488 p pair.2
    have combined := andIntro34761 p guard beforeEq
    have complete := andIntro35040 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro8488 p pair.2
    have combined := andIntro35078 p guard beforeEq
    have complete := andIntro35125 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro8624 p pair.2
    have combined := andIntro35078 p guard beforeEq
    have complete := andIntro35169 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local611 (p : Pattern) (guard : d122305 p = 1)
    (decreasing : bonus 158 (HazardPattern.afterPattern 10000 p (.walk 158)) < bonus 159 p) :
    NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 159 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 158) + NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 158))) + bonus 158 (HazardPattern.afterPattern 10000 p (.walk 158)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 158) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) < bonus 159 p at decreasing
  rw [gammaAfter611, at159] at decreasing
  have numeric := numeric611 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158))
  rw [oldBefore159, at159, literal, oldAfter611, gammaAfter611]
  exact numeric
theorem numeric612 (p : Pattern) (guard : d142666 p = 1) (decreasing : d167238 p < d15965 p) :
    d47866 p + d15965 p ≤ (2 : Int) + d47866 p + d167238 p := by
  have beforeRange := bonus_range 159 p
  rw [at159] at beforeRange
  have afterRange := bonus_range 158 (HazardPattern.afterPattern 10000 p (.push 158 (.stay 157)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 158 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 157))) ∧ bonus (HazardPattern.nextHero (.push 158 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 157))) ≤ 2 at afterRange
  rw [gammaAfter612] at afterRange
  have possibilities : (d15965 p = 1 ∧ d167238 p = 0) ∨ (d15965 p = 2 ∧ d167238 p = 0) ∨ (d15965 p = 2 ∧ d167238 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro9862 p pair.1
    have afterEq := eqIntro15179 p pair.2
    have combined := andIntro35441 p beforeEq guard
    have complete := andIntro35729 p afterEq combined
    have bound := compare10066 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro15179 p pair.2
    have combined := andIntro35767 p guard beforeEq
    have complete := andIntro35814 p afterEq combined
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro15238 p pair.2
    have combined := andIntro35767 p guard beforeEq
    have complete := andIntro35858 p combined afterEq
    have bound := compare10066 p complete
    omega
theorem local612 (p : Pattern) (guard : d142666 p = 1)
    (decreasing : bonus 158 (HazardPattern.afterPattern 10000 p (.push 158 (.stay 157))) < bonus 159 p) :
    NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 159 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 158 (.stay 157)) + NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 158 (.stay 157)))) + bonus 158 (HazardPattern.afterPattern 10000 p (.push 158 (.stay 157))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 158 (.stay 157)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 158 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 157))) < bonus 159 p at decreasing
  rw [gammaAfter612, at159] at decreasing
  have numeric := numeric612 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 158 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 157)))
  rw [oldBefore159, at159, literal, oldAfter612, gammaAfter612]
  exact numeric
theorem numeric613 (p : Pattern) (guard : d129472 p = 1) (decreasing : d0 p < d15965 p) :
    d47866 p + d15965 p ≤ (0 : Int) + d48251 p + d0 p := by
  have beforeRange := bonus_range 159 p
  rw [at159] at beforeRange
  have afterRange := bonus_range 138 (HazardPattern.afterPattern 10000 p (.walk 138))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) ∧ bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) ≤ 2 at afterRange
  rw [gammaAfter613] at afterRange
  have possibilities : (d15965 p = 1 ∧ d0 p = 0) ∨ (d15965 p = 2 ∧ d0 p = 0) ∨ (d15965 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro9862 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro36121 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare13658 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro36160 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare13659 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro36160 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare13658 p complete
    omega
theorem local613 (p : Pattern) (guard : d129472 p = 1)
    (decreasing : bonus 138 (HazardPattern.afterPattern 10000 p (.walk 138)) < bonus 159 p) :
    NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 159 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 138) + NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 138))) + bonus 138 (HazardPattern.afterPattern 10000 p (.walk 138)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 138) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) < bonus 159 p at decreasing
  rw [gammaAfter613, at159] at decreasing
  have numeric := numeric613 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138))
  rw [oldBefore159, at159, literal, oldAfter613, gammaAfter613]
  exact numeric
theorem numeric614 (p : Pattern) (guard : d122306 p = 1) (decreasing : d9291 p < d15965 p) :
    d47866 p + d15965 p ≤ (0 : Int) + d47866 p + d9291 p := by
  have beforeRange := bonus_range 159 p
  rw [at159] at beforeRange
  have afterRange := bonus_range 136 (HazardPattern.afterPattern 10000 p (.walk 136))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ∧ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ≤ 2 at afterRange
  rw [gammaAfter614] at afterRange
  have possibilities : (d15965 p = 1 ∧ d9291 p = 0) ∨ (d15965 p = 2 ∧ d9291 p = 0) ∨ (d15965 p = 2 ∧ d9291 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro9862 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro36404 p guard beforeEq
    have complete := andIntro36681 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro36719 p guard beforeEq
    have complete := andIntro36768 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro5906 p pair.2
    have combined := andIntro36719 p guard beforeEq
    have complete := andIntro36812 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local614 (p : Pattern) (guard : d122306 p = 1)
    (decreasing : bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 159 p) :
    NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 159 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 136) + NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 136))) + bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 136) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 159 p at decreasing
  rw [gammaAfter614, at159] at decreasing
  have numeric := numeric614 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136))
  rw [oldBefore159, at159, literal, oldAfter614, gammaAfter614]
  exact numeric
theorem numeric615 (p : Pattern) (guard : d169391 p = 1) (decreasing : d17560 p < d15965 p) :
    d47866 p + d15965 p ≤ (0 : Int) + d49280 p + d17560 p := by
  have beforeRange := bonus_range 159 p
  rw [at159] at beforeRange
  have afterRange := bonus_range 182 (HazardPattern.afterPattern 10000 p (.walk 182))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) ∧ bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) ≤ 2 at afterRange
  rw [gammaAfter615] at afterRange
  have possibilities : (d15965 p = 1 ∧ d17560 p = 0) ∨ (d15965 p = 2 ∧ d17560 p = 0) ∨ (d15965 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro9862 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro36813 p beforeEq guard
    have complete := andIntro34008 p combined afterEq
    have bound := compare13660 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro36814 p beforeEq guard
    have complete := andIntro34059 p afterEq combined
    have bound := compare13661 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro36814 p beforeEq guard
    have complete := andIntro34103 p afterEq combined
    have bound := compare13660 p complete
    omega
theorem local615 (p : Pattern) (guard : d169391 p = 1)
    (decreasing : bonus 182 (HazardPattern.afterPattern 10000 p (.walk 182)) < bonus 159 p) :
    NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 159 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 182) + NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 182))) + bonus 182 (HazardPattern.afterPattern 10000 p (.walk 182)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 182) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) < bonus 159 p at decreasing
  rw [gammaAfter615, at159] at decreasing
  have numeric := numeric615 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182))
  rw [oldBefore159, at159, literal, oldAfter615, gammaAfter615]
  exact numeric
theorem numeric616 (p : Pattern) (guard : d169397 p = 1) (decreasing : d23134 p < d15965 p) :
    d47866 p + d15965 p ≤ (0 : Int) + d47866 p + d23134 p := by
  have beforeRange := bonus_range 159 p
  rw [at159] at beforeRange
  have afterRange := bonus_range 180 (HazardPattern.afterPattern 10000 p (.walk 180))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) ∧ bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) ≤ 2 at afterRange
  rw [gammaAfter616] at afterRange
  have possibilities : (d15965 p = 1 ∧ d23134 p = 0) ∨ (d15965 p = 2 ∧ d23134 p = 0) ∨ (d15965 p = 2 ∧ d23134 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro9862 p pair.1
    have afterEq := eqIntro13202 p pair.2
    have combined := andIntro37121 p beforeEq guard
    have complete := andIntro37419 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro13202 p pair.2
    have combined := andIntro37457 p beforeEq guard
    have complete := andIntro37507 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro14634 p pair.1
    have afterEq := eqIntro13358 p pair.2
    have combined := andIntro37457 p beforeEq guard
    have complete := andIntro37551 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local616 (p : Pattern) (guard : d169397 p = 1)
    (decreasing : bonus 180 (HazardPattern.afterPattern 10000 p (.walk 180)) < bonus 159 p) :
    NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 159 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 180) + NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 180))) + bonus 180 (HazardPattern.afterPattern 10000 p (.walk 180)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 180) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) < bonus 159 p at decreasing
  rw [gammaAfter616, at159] at decreasing
  have numeric := numeric616 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180))
  rw [oldBefore159, at159, literal, oldAfter616, gammaAfter616]
  exact numeric
theorem numeric617 (p : Pattern) (guard : d126873 p = 1) (decreasing : d0 p < d17560 p) :
    d48388 p + d17560 p ≤ (0 : Int) + d48251 p + d0 p := by
  have beforeRange := bonus_range 160 p
  rw [at160] at beforeRange
  have afterRange := bonus_range 138 (HazardPattern.afterPattern 10000 p (.walk 138))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) ∧ bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) ≤ 2 at afterRange
  rw [gammaAfter617] at afterRange
  have possibilities : (d17560 p = 1 ∧ d0 p = 0) ∨ (d17560 p = 2 ∧ d0 p = 0) ∨ (d17560 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro37814 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare13662 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro37853 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare13663 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro37853 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare13662 p complete
    omega
theorem local617 (p : Pattern) (guard : d126873 p = 1)
    (decreasing : bonus 138 (HazardPattern.afterPattern 10000 p (.walk 138)) < bonus 160 p) :
    NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 160 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 138) + NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 138))) + bonus 138 (HazardPattern.afterPattern 10000 p (.walk 138)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 138) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) < bonus 160 p at decreasing
  rw [gammaAfter617, at160] at decreasing
  have numeric := numeric617 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138))
  rw [oldBefore160, at160, literal, oldAfter617, gammaAfter617]
  exact numeric
theorem numeric618 (p : Pattern) (guard : d100907 p = 1) (decreasing : d0 p < d17560 p) :
    d48388 p + d17560 p ≤ (2 : Int) + d171295 p + d0 p := by
  have beforeRange := bonus_range 160 p
  rw [at160] at beforeRange
  have afterRange := bonus_range 138 (HazardPattern.afterPattern 10000 p (.push 138 (.stay 116)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 138 (.stay 116))) (HazardPattern.afterPattern 10000 p (.push 138 (.stay 116))) ∧ bonus (HazardPattern.nextHero (.push 138 (.stay 116))) (HazardPattern.afterPattern 10000 p (.push 138 (.stay 116))) ≤ 2 at afterRange
  rw [gammaAfter618] at afterRange
  have possibilities : (d17560 p = 1 ∧ d0 p = 0) ∨ (d17560 p = 2 ∧ d0 p = 0) ∨ (d17560 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro37854 p guard beforeEq
    have complete := andIntro37855 p afterEq combined
    have bound := compare16492 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro37856 p guard beforeEq
    have complete := andIntro37857 p afterEq combined
    have bound := compare17860 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro37856 p guard beforeEq
    have complete := andIntro37858 p afterEq combined
    have bound := compare13664 p complete
    omega
theorem local618 (p : Pattern) (guard : d100907 p = 1)
    (decreasing : bonus 138 (HazardPattern.afterPattern 10000 p (.push 138 (.stay 116))) < bonus 160 p) :
    NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 160 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 138 (.stay 116)) + NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 138 (.stay 116)))) + bonus 138 (HazardPattern.afterPattern 10000 p (.push 138 (.stay 116))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 138 (.stay 116)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 138 (.stay 116))) (HazardPattern.afterPattern 10000 p (.push 138 (.stay 116))) < bonus 160 p at decreasing
  rw [gammaAfter618, at160] at decreasing
  have numeric := numeric618 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 138 (.stay 116))) (HazardPattern.afterPattern 10000 p (.push 138 (.stay 116)))
  rw [oldBefore160, at160, literal, oldAfter618, gammaAfter618]
  exact numeric
theorem numeric619 (p : Pattern) (guard : d169389 p = 1) (decreasing : d17560 p < d17560 p) :
    d48388 p + d17560 p ≤ (0 : Int) + d49280 p + d17560 p := by
  have beforeRange := bonus_range 160 p
  rw [at160] at beforeRange
  have afterRange := bonus_range 182 (HazardPattern.afterPattern 10000 p (.walk 182))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) ∧ bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) ≤ 2 at afterRange
  rw [gammaAfter619] at afterRange
  have possibilities : (d17560 p = 1 ∧ d17560 p = 0) ∨ (d17560 p = 2 ∧ d17560 p = 0) ∨ (d17560 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro37859 p beforeEq guard
    have complete := andIntro38077 p afterEq combined
    have bound := compare17861 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro38078 p guard beforeEq
    have complete := andIntro38128 p afterEq combined
    have bound := compare17862 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro38078 p guard beforeEq
    have complete := andIntro38172 p afterEq combined
    have bound := compare17861 p complete
    omega
theorem local619 (p : Pattern) (guard : d169389 p = 1)
    (decreasing : bonus 182 (HazardPattern.afterPattern 10000 p (.walk 182)) < bonus 160 p) :
    NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 160 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 182) + NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 182))) + bonus 182 (HazardPattern.afterPattern 10000 p (.walk 182)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 182) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) < bonus 160 p at decreasing
  rw [gammaAfter619, at160] at decreasing
  have numeric := numeric619 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182))
  rw [oldBefore160, at160, literal, oldAfter619, gammaAfter619]
  exact numeric
theorem numeric620 (p : Pattern) (guard : d171300 p = 1) (decreasing : d172575 p < d17560 p) :
    d48388 p + d17560 p ≤ (0 : Int) + d171439 p + d172575 p := by
  have beforeRange := bonus_range 160 p
  rw [at160] at beforeRange
  have afterRange := bonus_range 182 (HazardPattern.afterPattern 10000 p (.push 182 (.stay 204)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 182 (.stay 204))) (HazardPattern.afterPattern 10000 p (.push 182 (.stay 204))) ∧ bonus (HazardPattern.nextHero (.push 182 (.stay 204))) (HazardPattern.afterPattern 10000 p (.push 182 (.stay 204))) ≤ 2 at afterRange
  rw [gammaAfter620] at afterRange
  have possibilities : (d17560 p = 1 ∧ d172575 p = 0) ∨ (d17560 p = 2 ∧ d172575 p = 0) ∨ (d17560 p = 2 ∧ d172575 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro15724 p pair.2
    have combined := andIntro38544 p beforeEq guard
    have complete := andIntro38545 p combined afterEq
    have bound := compare17863 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro15724 p pair.2
    have combined := andIntro38584 p beforeEq guard
    have complete := andIntro38545 p combined afterEq
    have bound := compare17864 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro15796 p pair.2
    have combined := andIntro38584 p beforeEq guard
    have complete := andIntro38585 p combined afterEq
    have bound := compare17863 p complete
    omega
theorem local620 (p : Pattern) (guard : d171300 p = 1)
    (decreasing : bonus 182 (HazardPattern.afterPattern 10000 p (.push 182 (.stay 204))) < bonus 160 p) :
    NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 160 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 182 (.stay 204)) + NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 182 (.stay 204)))) + bonus 182 (HazardPattern.afterPattern 10000 p (.push 182 (.stay 204))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 182 (.stay 204)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 182 (.stay 204))) (HazardPattern.afterPattern 10000 p (.push 182 (.stay 204))) < bonus 160 p at decreasing
  rw [gammaAfter620, at160] at decreasing
  have numeric := numeric620 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 182 (.stay 204))) (HazardPattern.afterPattern 10000 p (.push 182 (.stay 204)))
  rw [oldBefore160, at160, literal, oldAfter620, gammaAfter620]
  exact numeric
theorem numeric621 (p : Pattern) (guard : d128579 p = 1) (decreasing : d18533 p < d17560 p) :
    d48388 p + d17560 p ≤ (0 : Int) + d48547 p + d18533 p := by
  have beforeRange := bonus_range 160 p
  rw [at160] at beforeRange
  have afterRange := bonus_range 161 (HazardPattern.afterPattern 10000 p (.walk 161))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) ∧ bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) ≤ 2 at afterRange
  rw [gammaAfter621] at afterRange
  have possibilities : (d17560 p = 1 ∧ d18533 p = 0) ∨ (d17560 p = 2 ∧ d18533 p = 0) ∨ (d17560 p = 2 ∧ d18533 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro10408 p pair.2
    have combined := andIntro38910 p beforeEq guard
    have complete := andIntro39022 p afterEq combined
    have bound := compare17865 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10408 p pair.2
    have combined := andIntro39061 p guard beforeEq
    have complete := andIntro39095 p afterEq combined
    have bound := compare17866 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10478 p pair.2
    have combined := andIntro39061 p guard beforeEq
    have complete := andIntro39123 p afterEq combined
    have bound := compare17865 p complete
    omega
theorem local621 (p : Pattern) (guard : d128579 p = 1)
    (decreasing : bonus 161 (HazardPattern.afterPattern 10000 p (.walk 161)) < bonus 160 p) :
    NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 160 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 161) + NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 161))) + bonus 161 (HazardPattern.afterPattern 10000 p (.walk 161)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 161) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) < bonus 160 p at decreasing
  rw [gammaAfter621, at160] at decreasing
  have numeric := numeric621 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161))
  rw [oldBefore160, at160, literal, oldAfter621, gammaAfter621]
  exact numeric
theorem numeric622 (p : Pattern) (guard : d173704 p = 1) (decreasing : d174647 p < d17560 p) :
    d48388 p + d17560 p ≤ (2 : Int) + d173755 p + d174647 p := by
  have beforeRange := bonus_range 160 p
  rw [at160] at beforeRange
  have afterRange := bonus_range 161 (HazardPattern.afterPattern 10000 p (.push 161 (.stay 162)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 161 (.stay 162))) (HazardPattern.afterPattern 10000 p (.push 161 (.stay 162))) ∧ bonus (HazardPattern.nextHero (.push 161 (.stay 162))) (HazardPattern.afterPattern 10000 p (.push 161 (.stay 162))) ≤ 2 at afterRange
  rw [gammaAfter622] at afterRange
  have possibilities : (d17560 p = 1 ∧ d174647 p = 0) ∨ (d17560 p = 2 ∧ d174647 p = 0) ∨ (d17560 p = 2 ∧ d174647 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro15950 p pair.2
    have combined := andIntro39235 p beforeEq guard
    have complete := andIntro39347 p afterEq combined
    have bound := compare20385 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro15950 p pair.2
    have combined := andIntro39380 p beforeEq guard
    have complete := andIntro39414 p afterEq combined
    have bound := compare21612 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro16020 p pair.2
    have combined := andIntro39380 p beforeEq guard
    have complete := andIntro39442 p combined afterEq
    have bound := compare17867 p complete
    omega
theorem local622 (p : Pattern) (guard : d173704 p = 1)
    (decreasing : bonus 161 (HazardPattern.afterPattern 10000 p (.push 161 (.stay 162))) < bonus 160 p) :
    NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 160 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 161 (.stay 162)) + NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 161 (.stay 162)))) + bonus 161 (HazardPattern.afterPattern 10000 p (.push 161 (.stay 162))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 161 (.stay 162)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 161 (.stay 162))) (HazardPattern.afterPattern 10000 p (.push 161 (.stay 162))) < bonus 160 p at decreasing
  rw [gammaAfter622, at160] at decreasing
  have numeric := numeric622 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 161 (.stay 162))) (HazardPattern.afterPattern 10000 p (.push 161 (.stay 162)))
  rw [oldBefore160, at160, literal, oldAfter622, gammaAfter622]
  exact numeric
theorem numeric623 (p : Pattern) (guard : d129471 p = 1) (decreasing : d15965 p < d17560 p) :
    d48388 p + d17560 p ≤ (0 : Int) + d47866 p + d15965 p := by
  have beforeRange := bonus_range 160 p
  rw [at160] at beforeRange
  have afterRange := bonus_range 159 (HazardPattern.afterPattern 10000 p (.walk 159))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ∧ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ≤ 2 at afterRange
  rw [gammaAfter623] at afterRange
  have possibilities : (d17560 p = 1 ∧ d15965 p = 0) ∨ (d17560 p = 2 ∧ d15965 p = 0) ∨ (d17560 p = 2 ∧ d15965 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro39726 p beforeEq guard
    have complete := andIntro40006 p afterEq combined
    have bound := compare21613 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro40044 p guard beforeEq
    have complete := andIntro40094 p afterEq combined
    have bound := compare21614 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro9862 p pair.2
    have combined := andIntro40044 p guard beforeEq
    have complete := andIntro40138 p afterEq combined
    have bound := compare21613 p complete
    omega
theorem local623 (p : Pattern) (guard : d129471 p = 1)
    (decreasing : bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 160 p) :
    NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 160 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 159) + NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 159))) + bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 159) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 160 p at decreasing
  rw [gammaAfter623, at160] at decreasing
  have numeric := numeric623 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159))
  rw [oldBefore160, at160, literal, oldAfter623, gammaAfter623]
  exact numeric
theorem numeric624 (p : Pattern) (guard : d159762 p = 1) (decreasing : d177183 p < d17560 p) :
    d48388 p + d17560 p ≤ (2 : Int) + d47866 p + d177183 p := by
  have beforeRange := bonus_range 160 p
  rw [at160] at beforeRange
  have afterRange := bonus_range 159 (HazardPattern.afterPattern 10000 p (.push 159 (.stay 158)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 159 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 159 (.stay 158))) ∧ bonus (HazardPattern.nextHero (.push 159 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 159 (.stay 158))) ≤ 2 at afterRange
  rw [gammaAfter624] at afterRange
  have possibilities : (d17560 p = 1 ∧ d177183 p = 0) ∨ (d17560 p = 2 ∧ d177183 p = 0) ∨ (d17560 p = 2 ∧ d177183 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro16296 p pair.2
    have combined := andIntro40434 p beforeEq guard
    have complete := andIntro40697 p afterEq combined
    have bound := compare23282 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro16296 p pair.2
    have combined := andIntro40735 p guard beforeEq
    have complete := andIntro40779 p afterEq combined
    have bound := compare24094 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro16402 p pair.2
    have combined := andIntro40735 p guard beforeEq
    have complete := andIntro40823 p combined afterEq
    have bound := compare21615 p complete
    omega
theorem local624 (p : Pattern) (guard : d159762 p = 1)
    (decreasing : bonus 159 (HazardPattern.afterPattern 10000 p (.push 159 (.stay 158))) < bonus 160 p) :
    NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 160 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 159 (.stay 158)) + NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 159 (.stay 158)))) + bonus 159 (HazardPattern.afterPattern 10000 p (.push 159 (.stay 158))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 159 (.stay 158)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 159 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 159 (.stay 158))) < bonus 160 p at decreasing
  rw [gammaAfter624, at160] at decreasing
  have numeric := numeric624 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 159 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 159 (.stay 158)))
  rw [oldBefore160, at160, literal, oldAfter624, gammaAfter624]
  exact numeric
theorem numeric625 (p : Pattern) (guard : d180907 p = 1) (decreasing : d17560 p < d17560 p) :
    d48388 p + d17560 p ≤ (0 : Int) + d47866 p + d17560 p := by
  have beforeRange := bonus_range 160 p
  rw [at160] at beforeRange
  have afterRange := bonus_range 181 (HazardPattern.afterPattern 10000 p (.walk 181))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ∧ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ≤ 2 at afterRange
  rw [gammaAfter625] at afterRange
  have possibilities : (d17560 p = 1 ∧ d17560 p = 0) ∨ (d17560 p = 2 ∧ d17560 p = 0) ∨ (d17560 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro40824 p beforeEq guard
    have complete := andIntro38077 p afterEq combined
    have bound := compare21613 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro40825 p beforeEq guard
    have complete := andIntro38128 p afterEq combined
    have bound := compare21614 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro40825 p beforeEq guard
    have complete := andIntro38172 p afterEq combined
    have bound := compare21613 p complete
    omega
theorem local625 (p : Pattern) (guard : d180907 p = 1)
    (decreasing : bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 160 p) :
    NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 160 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 181) + NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 181))) + bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 181) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 160 p at decreasing
  rw [gammaAfter625, at160] at decreasing
  have numeric := numeric625 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181))
  rw [oldBefore160, at160, literal, oldAfter625, gammaAfter625]
  exact numeric
theorem numeric626 (p : Pattern) (guard : d180908 p = 1) (decreasing : d19737 p < d18533 p) :
    d48547 p + d18533 p ≤ (0 : Int) + d48749 p + d19737 p := by
  have beforeRange := bonus_range 161 p
  rw [at161] at beforeRange
  have afterRange := bonus_range 162 (HazardPattern.afterPattern 10000 p (.walk 162))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) ∧ bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) ≤ 2 at afterRange
  rw [gammaAfter626] at afterRange
  have possibilities : (d18533 p = 1 ∧ d19737 p = 0) ∨ (d18533 p = 2 ∧ d19737 p = 0) ∨ (d18533 p = 2 ∧ d19737 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10478 p pair.1
    have afterEq := eqIntro11154 p pair.2
    have combined := andIntro40937 p beforeEq guard
    have complete := andIntro41049 p afterEq combined
    have bound := compare24095 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro11154 p pair.2
    have combined := andIntro41082 p beforeEq guard
    have complete := andIntro41116 p afterEq combined
    have bound := compare24096 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro11224 p pair.2
    have combined := andIntro41082 p beforeEq guard
    have complete := andIntro41144 p afterEq combined
    have bound := compare24095 p complete
    omega
theorem local626 (p : Pattern) (guard : d180908 p = 1)
    (decreasing : bonus 162 (HazardPattern.afterPattern 10000 p (.walk 162)) < bonus 161 p) :
    NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 161 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 162) + NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 162))) + bonus 162 (HazardPattern.afterPattern 10000 p (.walk 162)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 162) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) < bonus 161 p at decreasing
  rw [gammaAfter626, at161] at decreasing
  have numeric := numeric626 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162))
  rw [oldBefore161, at161, literal, oldAfter626, gammaAfter626]
  exact numeric
theorem numeric627 (p : Pattern) (guard : d181811 p = 1) (decreasing : d182839 p < d18533 p) :
    d48547 p + d18533 p ≤ (2 : Int) + d181866 p + d182839 p := by
  have beforeRange := bonus_range 161 p
  rw [at161] at beforeRange
  have afterRange := bonus_range 162 (HazardPattern.afterPattern 10000 p (.push 162 (.stay 163)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 162 (.stay 163))) (HazardPattern.afterPattern 10000 p (.push 162 (.stay 163))) ∧ bonus (HazardPattern.nextHero (.push 162 (.stay 163))) (HazardPattern.afterPattern 10000 p (.push 162 (.stay 163))) ≤ 2 at afterRange
  rw [gammaAfter627] at afterRange
  have possibilities : (d18533 p = 1 ∧ d182839 p = 0) ∨ (d18533 p = 2 ∧ d182839 p = 0) ∨ (d18533 p = 2 ∧ d182839 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10478 p pair.1
    have afterEq := eqIntro16710 p pair.2
    have combined := andIntro41256 p beforeEq guard
    have complete := andIntro41368 p afterEq combined
    have bound := compare24097 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro16710 p pair.2
    have combined := andIntro41401 p beforeEq guard
    have complete := andIntro41435 p afterEq combined
    have bound := compare24098 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro16780 p pair.2
    have combined := andIntro41401 p beforeEq guard
    have complete := andIntro41463 p combined afterEq
    have bound := compare24097 p complete
    omega
theorem local627 (p : Pattern) (guard : d181811 p = 1)
    (decreasing : bonus 162 (HazardPattern.afterPattern 10000 p (.push 162 (.stay 163))) < bonus 161 p) :
    NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 161 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 162 (.stay 163)) + NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 162 (.stay 163)))) + bonus 162 (HazardPattern.afterPattern 10000 p (.push 162 (.stay 163))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 162 (.stay 163)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 162 (.stay 163))) (HazardPattern.afterPattern 10000 p (.push 162 (.stay 163))) < bonus 161 p at decreasing
  rw [gammaAfter627, at161] at decreasing
  have numeric := numeric627 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 162 (.stay 163))) (HazardPattern.afterPattern 10000 p (.push 162 (.stay 163)))
  rw [oldBefore161, at161, literal, oldAfter627, gammaAfter627]
  exact numeric
theorem numeric628 (p : Pattern) (guard : d128579 p = 1) (decreasing : d17560 p < d18533 p) :
    d48547 p + d18533 p ≤ (0 : Int) + d48388 p + d17560 p := by
  have beforeRange := bonus_range 161 p
  rw [at161] at beforeRange
  have afterRange := bonus_range 160 (HazardPattern.afterPattern 10000 p (.walk 160))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) ∧ bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) ≤ 2 at afterRange
  rw [gammaAfter628] at afterRange
  have possibilities : (d18533 p = 1 ∧ d17560 p = 0) ∨ (d18533 p = 2 ∧ d17560 p = 0) ∨ (d18533 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10478 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro41464 p guard beforeEq
    have complete := andIntro41576 p afterEq combined
    have bound := compare24099 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro41577 p guard beforeEq
    have complete := andIntro41611 p afterEq combined
    have bound := compare24100 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro41577 p guard beforeEq
    have complete := andIntro41639 p afterEq combined
    have bound := compare24099 p complete
    omega
theorem local628 (p : Pattern) (guard : d128579 p = 1)
    (decreasing : bonus 160 (HazardPattern.afterPattern 10000 p (.walk 160)) < bonus 161 p) :
    NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 161 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 160) + NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 160))) + bonus 160 (HazardPattern.afterPattern 10000 p (.walk 160)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 160) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) < bonus 161 p at decreasing
  rw [gammaAfter628, at161] at decreasing
  have numeric := numeric628 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160))
  rw [oldBefore161, at161, literal, oldAfter628, gammaAfter628]
  exact numeric
theorem numeric629 (p : Pattern) (guard : d163684 p = 1) (decreasing : d186172 p < d18533 p) :
    d48547 p + d18533 p ≤ (2 : Int) + d184679 p + d186172 p := by
  have beforeRange := bonus_range 161 p
  rw [at161] at beforeRange
  have afterRange := bonus_range 160 (HazardPattern.afterPattern 10000 p (.push 160 (.stay 159)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 160 (.stay 159))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 159))) ∧ bonus (HazardPattern.nextHero (.push 160 (.stay 159))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 159))) ≤ 2 at afterRange
  rw [gammaAfter629] at afterRange
  have possibilities : (d18533 p = 1 ∧ d186172 p = 0) ∨ (d18533 p = 2 ∧ d186172 p = 0) ∨ (d18533 p = 2 ∧ d186172 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10478 p pair.1
    have afterEq := eqIntro17097 p pair.2
    have combined := andIntro41751 p beforeEq guard
    have complete := andIntro41752 p combined afterEq
    have bound := compare24101 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro17097 p pair.2
    have combined := andIntro41785 p guard beforeEq
    have complete := andIntro41752 p combined afterEq
    have bound := compare24102 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro17211 p pair.2
    have combined := andIntro41785 p guard beforeEq
    have complete := andIntro41786 p combined afterEq
    have bound := compare24101 p complete
    omega
theorem local629 (p : Pattern) (guard : d163684 p = 1)
    (decreasing : bonus 160 (HazardPattern.afterPattern 10000 p (.push 160 (.stay 159))) < bonus 161 p) :
    NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 161 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 160 (.stay 159)) + NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 160 (.stay 159)))) + bonus 160 (HazardPattern.afterPattern 10000 p (.push 160 (.stay 159))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 160 (.stay 159)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 160 (.stay 159))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 159))) < bonus 161 p at decreasing
  rw [gammaAfter629, at161] at decreasing
  have numeric := numeric629 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 160 (.stay 159))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 159)))
  rw [oldBefore161, at161, literal, oldAfter629, gammaAfter629]
  exact numeric
end NetHack.Soko22Hazard87
