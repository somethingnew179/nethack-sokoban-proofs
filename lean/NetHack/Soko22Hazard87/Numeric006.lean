import NetHack.Soko22Hazard87.Numeric005
import NetHack.Soko22Hazard87.AndIntroBlocks0092
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric420 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 125 p
  rw [at125] at beforeRange
  have afterRange := bonus_range 148 (HazardPattern.afterPattern 10000 p (.walk 148))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ∧ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ≤ 2 at afterRange
  rw [gammaAfter420] at afterRange
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
theorem local420 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 148) + NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 148))) + bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 148) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 125 p at decreasing
  rw [gammaAfter420, at125] at decreasing
  have numeric := numeric420 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148))
  rw [oldBefore125, at125, literal, oldAfter420, gammaAfter420]
  exact numeric
theorem numeric421 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 125 p
  rw [at125] at beforeRange
  have afterRange := bonus_range 146 (HazardPattern.afterPattern 10000 p (.walk 146))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ∧ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ≤ 2 at afterRange
  rw [gammaAfter421] at afterRange
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
theorem local421 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 146) + NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) + bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 146) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 125 p at decreasing
  rw [gammaAfter421, at125] at decreasing
  have numeric := numeric421 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146))
  rw [oldBefore125, at125, literal, oldAfter421, gammaAfter421]
  exact numeric
theorem numeric422 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 126 p
  rw [at126] at beforeRange
  have afterRange := bonus_range 104 (HazardPattern.afterPattern 10000 p (.walk 104))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ∧ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ≤ 2 at afterRange
  rw [gammaAfter422] at afterRange
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
theorem local422 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 104) + NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 104))) + bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 104) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 126 p at decreasing
  rw [gammaAfter422, at126] at decreasing
  have numeric := numeric422 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104))
  rw [oldBefore126, at126, literal, oldAfter422, gammaAfter422]
  exact numeric
theorem numeric423 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 126 p
  rw [at126] at beforeRange
  have afterRange := bonus_range 104 (HazardPattern.afterPattern 10000 p (.push 104 (.stay 82)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 104 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 82))) ∧ bonus (HazardPattern.nextHero (.push 104 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 82))) ≤ 2 at afterRange
  rw [gammaAfter423] at afterRange
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
theorem local423 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 104 (HazardPattern.afterPattern 10000 p (.push 104 (.stay 82))) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 104 (.stay 82)) + NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 104 (.stay 82)))) + bonus 104 (HazardPattern.afterPattern 10000 p (.push 104 (.stay 82))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 104 (.stay 82)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 104 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 82))) < bonus 126 p at decreasing
  rw [gammaAfter423, at126] at decreasing
  have numeric := numeric423 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 104 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 82)))
  rw [oldBefore126, at126, literal, oldAfter423, gammaAfter423]
  exact numeric
theorem numeric424 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 126 p
  rw [at126] at beforeRange
  have afterRange := bonus_range 148 (HazardPattern.afterPattern 10000 p (.walk 148))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ∧ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ≤ 2 at afterRange
  rw [gammaAfter424] at afterRange
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
theorem local424 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 148) + NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 148))) + bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 148) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 126 p at decreasing
  rw [gammaAfter424, at126] at decreasing
  have numeric := numeric424 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148))
  rw [oldBefore126, at126, literal, oldAfter424, gammaAfter424]
  exact numeric
theorem numeric425 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 126 p
  rw [at126] at beforeRange
  have afterRange := bonus_range 148 (HazardPattern.afterPattern 10000 p (.push 148 (.stay 170)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 148 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 170))) ∧ bonus (HazardPattern.nextHero (.push 148 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 170))) ≤ 2 at afterRange
  rw [gammaAfter425] at afterRange
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
theorem local425 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 148 (HazardPattern.afterPattern 10000 p (.push 148 (.stay 170))) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 148 (.stay 170)) + NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 148 (.stay 170)))) + bonus 148 (HazardPattern.afterPattern 10000 p (.push 148 (.stay 170))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 148 (.stay 170)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 148 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 170))) < bonus 126 p at decreasing
  rw [gammaAfter425, at126] at decreasing
  have numeric := numeric425 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 148 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 170)))
  rw [oldBefore126, at126, literal, oldAfter425, gammaAfter425]
  exact numeric
theorem numeric426 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 126 p
  rw [at126] at beforeRange
  have afterRange := bonus_range 127 (HazardPattern.afterPattern 10000 p (.walk 127))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ∧ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ≤ 2 at afterRange
  rw [gammaAfter426] at afterRange
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
theorem local426 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 127) + NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) + bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 127) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 126 p at decreasing
  rw [gammaAfter426, at126] at decreasing
  have numeric := numeric426 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127))
  rw [oldBefore126, at126, literal, oldAfter426, gammaAfter426]
  exact numeric
theorem numeric427 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 126 p
  rw [at126] at beforeRange
  have afterRange := bonus_range 127 (HazardPattern.afterPattern 10000 p (.push 127 (.stay 128)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 127 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 128))) ∧ bonus (HazardPattern.nextHero (.push 127 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 128))) ≤ 2 at afterRange
  rw [gammaAfter427] at afterRange
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
theorem local427 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 127 (HazardPattern.afterPattern 10000 p (.push 127 (.stay 128))) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 127 (.stay 128)) + NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 127 (.stay 128)))) + bonus 127 (HazardPattern.afterPattern 10000 p (.push 127 (.stay 128))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 127 (.stay 128)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 127 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 128))) < bonus 126 p at decreasing
  rw [gammaAfter427, at126] at decreasing
  have numeric := numeric427 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 127 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 128)))
  rw [oldBefore126, at126, literal, oldAfter427, gammaAfter427]
  exact numeric
theorem numeric428 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 126 p
  rw [at126] at beforeRange
  have afterRange := bonus_range 125 (HazardPattern.afterPattern 10000 p (.walk 125))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ∧ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ≤ 2 at afterRange
  rw [gammaAfter428] at afterRange
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
theorem local428 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 125) + NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) + bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 125) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 126 p at decreasing
  rw [gammaAfter428, at126] at decreasing
  have numeric := numeric428 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125))
  rw [oldBefore126, at126, literal, oldAfter428, gammaAfter428]
  exact numeric
theorem numeric429 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 126 p
  rw [at126] at beforeRange
  have afterRange := bonus_range 125 (HazardPattern.afterPattern 10000 p (.push 125 (.stay 124)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 125 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 124))) ∧ bonus (HazardPattern.nextHero (.push 125 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 124))) ≤ 2 at afterRange
  rw [gammaAfter429] at afterRange
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
theorem local429 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 125 (HazardPattern.afterPattern 10000 p (.push 125 (.stay 124))) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 125 (.stay 124)) + NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 125 (.stay 124)))) + bonus 125 (HazardPattern.afterPattern 10000 p (.push 125 (.stay 124))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 125 (.stay 124)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 125 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 124))) < bonus 126 p at decreasing
  rw [gammaAfter429, at126] at decreasing
  have numeric := numeric429 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 125 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 124)))
  rw [oldBefore126, at126, literal, oldAfter429, gammaAfter429]
  exact numeric
theorem numeric430 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 126 p
  rw [at126] at beforeRange
  have afterRange := bonus_range 105 (HazardPattern.afterPattern 10000 p (.walk 105))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ∧ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ≤ 2 at afterRange
  rw [gammaAfter430] at afterRange
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
theorem local430 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 105) + NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 105))) + bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 105) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 126 p at decreasing
  rw [gammaAfter430, at126] at decreasing
  have numeric := numeric430 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105))
  rw [oldBefore126, at126, literal, oldAfter430, gammaAfter430]
  exact numeric
theorem numeric431 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 126 p
  rw [at126] at beforeRange
  have afterRange := bonus_range 103 (HazardPattern.afterPattern 10000 p (.walk 103))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ∧ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ≤ 2 at afterRange
  rw [gammaAfter431] at afterRange
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
theorem local431 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 103) + NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 103))) + bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 103) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 126 p at decreasing
  rw [gammaAfter431, at126] at decreasing
  have numeric := numeric431 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103))
  rw [oldBefore126, at126, literal, oldAfter431, gammaAfter431]
  exact numeric
theorem numeric432 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 126 p
  rw [at126] at beforeRange
  have afterRange := bonus_range 149 (HazardPattern.afterPattern 10000 p (.walk 149))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ∧ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ≤ 2 at afterRange
  rw [gammaAfter432] at afterRange
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
theorem local432 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 149) + NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) + bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 149) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 126 p at decreasing
  rw [gammaAfter432, at126] at decreasing
  have numeric := numeric432 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149))
  rw [oldBefore126, at126, literal, oldAfter432, gammaAfter432]
  exact numeric
theorem numeric433 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 126 p
  rw [at126] at beforeRange
  have afterRange := bonus_range 147 (HazardPattern.afterPattern 10000 p (.walk 147))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ∧ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ≤ 2 at afterRange
  rw [gammaAfter433] at afterRange
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
theorem local433 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 147) + NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) + bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 147) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 126 p at decreasing
  rw [gammaAfter433, at126] at decreasing
  have numeric := numeric433 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147))
  rw [oldBefore126, at126, literal, oldAfter433, gammaAfter433]
  exact numeric
theorem numeric434 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 127 p
  rw [at127] at beforeRange
  have afterRange := bonus_range 105 (HazardPattern.afterPattern 10000 p (.walk 105))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ∧ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ≤ 2 at afterRange
  rw [gammaAfter434] at afterRange
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
theorem local434 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 127 p) :
    NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 127 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 105) + NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 105))) + bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 105) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 127 p at decreasing
  rw [gammaAfter434, at127] at decreasing
  have numeric := numeric434 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105))
  rw [oldBefore127, at127, literal, oldAfter434, gammaAfter434]
  exact numeric
theorem numeric435 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 127 p
  rw [at127] at beforeRange
  have afterRange := bonus_range 105 (HazardPattern.afterPattern 10000 p (.push 105 (.stay 83)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 105 (.stay 83))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 83))) ∧ bonus (HazardPattern.nextHero (.push 105 (.stay 83))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 83))) ≤ 2 at afterRange
  rw [gammaAfter435] at afterRange
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
theorem local435 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 105 (HazardPattern.afterPattern 10000 p (.push 105 (.stay 83))) < bonus 127 p) :
    NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 127 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 105 (.stay 83)) + NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 105 (.stay 83)))) + bonus 105 (HazardPattern.afterPattern 10000 p (.push 105 (.stay 83))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 105 (.stay 83)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 105 (.stay 83))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 83))) < bonus 127 p at decreasing
  rw [gammaAfter435, at127] at decreasing
  have numeric := numeric435 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 105 (.stay 83))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 83)))
  rw [oldBefore127, at127, literal, oldAfter435, gammaAfter435]
  exact numeric
theorem numeric436 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 127 p
  rw [at127] at beforeRange
  have afterRange := bonus_range 149 (HazardPattern.afterPattern 10000 p (.walk 149))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ∧ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ≤ 2 at afterRange
  rw [gammaAfter436] at afterRange
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
theorem local436 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 127 p) :
    NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 127 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 149) + NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) + bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 149) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 127 p at decreasing
  rw [gammaAfter436, at127] at decreasing
  have numeric := numeric436 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149))
  rw [oldBefore127, at127, literal, oldAfter436, gammaAfter436]
  exact numeric
theorem numeric437 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 127 p
  rw [at127] at beforeRange
  have afterRange := bonus_range 149 (HazardPattern.afterPattern 10000 p (.push 149 (.stay 171)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 149 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 171))) ∧ bonus (HazardPattern.nextHero (.push 149 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 171))) ≤ 2 at afterRange
  rw [gammaAfter437] at afterRange
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
theorem local437 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 149 (HazardPattern.afterPattern 10000 p (.push 149 (.stay 171))) < bonus 127 p) :
    NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 127 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 149 (.stay 171)) + NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 149 (.stay 171)))) + bonus 149 (HazardPattern.afterPattern 10000 p (.push 149 (.stay 171))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 149 (.stay 171)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 149 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 171))) < bonus 127 p at decreasing
  rw [gammaAfter437, at127] at decreasing
  have numeric := numeric437 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 149 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 171)))
  rw [oldBefore127, at127, literal, oldAfter437, gammaAfter437]
  exact numeric
theorem numeric438 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 127 p
  rw [at127] at beforeRange
  have afterRange := bonus_range 128 (HazardPattern.afterPattern 10000 p (.walk 128))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) ∧ bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) ≤ 2 at afterRange
  rw [gammaAfter438] at afterRange
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
theorem local438 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 128 (HazardPattern.afterPattern 10000 p (.walk 128)) < bonus 127 p) :
    NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 127 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 128) + NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 128))) + bonus 128 (HazardPattern.afterPattern 10000 p (.walk 128)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 128) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) < bonus 127 p at decreasing
  rw [gammaAfter438, at127] at decreasing
  have numeric := numeric438 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128))
  rw [oldBefore127, at127, literal, oldAfter438, gammaAfter438]
  exact numeric
theorem numeric439 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 127 p
  rw [at127] at beforeRange
  have afterRange := bonus_range 126 (HazardPattern.afterPattern 10000 p (.walk 126))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ∧ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ≤ 2 at afterRange
  rw [gammaAfter439] at afterRange
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
theorem local439 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 127 p) :
    NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 127 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 126) + NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 126))) + bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 126) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 127 p at decreasing
  rw [gammaAfter439, at127] at decreasing
  have numeric := numeric439 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126))
  rw [oldBefore127, at127, literal, oldAfter439, gammaAfter439]
  exact numeric
theorem numeric440 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 127 p
  rw [at127] at beforeRange
  have afterRange := bonus_range 126 (HazardPattern.afterPattern 10000 p (.push 126 (.stay 125)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 126 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 125))) ∧ bonus (HazardPattern.nextHero (.push 126 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 125))) ≤ 2 at afterRange
  rw [gammaAfter440] at afterRange
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
theorem local440 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 126 (HazardPattern.afterPattern 10000 p (.push 126 (.stay 125))) < bonus 127 p) :
    NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 127 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 126 (.stay 125)) + NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 126 (.stay 125)))) + bonus 126 (HazardPattern.afterPattern 10000 p (.push 126 (.stay 125))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 126 (.stay 125)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 126 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 125))) < bonus 127 p at decreasing
  rw [gammaAfter440, at127] at decreasing
  have numeric := numeric440 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 126 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 125)))
  rw [oldBefore127, at127, literal, oldAfter440, gammaAfter440]
  exact numeric
theorem numeric441 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 127 p
  rw [at127] at beforeRange
  have afterRange := bonus_range 106 (HazardPattern.afterPattern 10000 p (.walk 106))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) ∧ bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) ≤ 2 at afterRange
  rw [gammaAfter441] at afterRange
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
theorem local441 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 106 (HazardPattern.afterPattern 10000 p (.walk 106)) < bonus 127 p) :
    NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 127 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 106) + NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 106))) + bonus 106 (HazardPattern.afterPattern 10000 p (.walk 106)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 106) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) < bonus 127 p at decreasing
  rw [gammaAfter441, at127] at decreasing
  have numeric := numeric441 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106))
  rw [oldBefore127, at127, literal, oldAfter441, gammaAfter441]
  exact numeric
theorem numeric442 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 127 p
  rw [at127] at beforeRange
  have afterRange := bonus_range 104 (HazardPattern.afterPattern 10000 p (.walk 104))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ∧ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ≤ 2 at afterRange
  rw [gammaAfter442] at afterRange
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
theorem local442 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 127 p) :
    NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 127 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 104) + NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 104))) + bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 104) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 127 p at decreasing
  rw [gammaAfter442, at127] at decreasing
  have numeric := numeric442 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104))
  rw [oldBefore127, at127, literal, oldAfter442, gammaAfter442]
  exact numeric
theorem numeric443 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 127 p
  rw [at127] at beforeRange
  have afterRange := bonus_range 150 (HazardPattern.afterPattern 10000 p (.walk 150))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) ∧ bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) ≤ 2 at afterRange
  rw [gammaAfter443] at afterRange
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
theorem local443 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 150 (HazardPattern.afterPattern 10000 p (.walk 150)) < bonus 127 p) :
    NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 127 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 150) + NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 150))) + bonus 150 (HazardPattern.afterPattern 10000 p (.walk 150)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 150) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) < bonus 127 p at decreasing
  rw [gammaAfter443, at127] at decreasing
  have numeric := numeric443 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150))
  rw [oldBefore127, at127, literal, oldAfter443, gammaAfter443]
  exact numeric
theorem numeric444 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 127 p
  rw [at127] at beforeRange
  have afterRange := bonus_range 148 (HazardPattern.afterPattern 10000 p (.walk 148))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ∧ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ≤ 2 at afterRange
  rw [gammaAfter444] at afterRange
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
theorem local444 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 127 p) :
    NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 127 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 148) + NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 148))) + bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 148) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 127 p at decreasing
  rw [gammaAfter444, at127] at decreasing
  have numeric := numeric444 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148))
  rw [oldBefore127, at127, literal, oldAfter444, gammaAfter444]
  exact numeric
theorem numeric445 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 128 p
  rw [at128] at beforeRange
  have afterRange := bonus_range 106 (HazardPattern.afterPattern 10000 p (.walk 106))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) ∧ bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) ≤ 2 at afterRange
  rw [gammaAfter445] at afterRange
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
theorem local445 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 106 (HazardPattern.afterPattern 10000 p (.walk 106)) < bonus 128 p) :
    NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 128 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 106) + NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 106))) + bonus 106 (HazardPattern.afterPattern 10000 p (.walk 106)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 106) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) < bonus 128 p at decreasing
  rw [gammaAfter445, at128] at decreasing
  have numeric := numeric445 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106))
  rw [oldBefore128, at128, literal, oldAfter445, gammaAfter445]
  exact numeric
theorem numeric446 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 128 p
  rw [at128] at beforeRange
  have afterRange := bonus_range 106 (HazardPattern.afterPattern 10000 p (.push 106 (.stay 84)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 106 (.stay 84))) (HazardPattern.afterPattern 10000 p (.push 106 (.stay 84))) ∧ bonus (HazardPattern.nextHero (.push 106 (.stay 84))) (HazardPattern.afterPattern 10000 p (.push 106 (.stay 84))) ≤ 2 at afterRange
  rw [gammaAfter446] at afterRange
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
theorem local446 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 106 (HazardPattern.afterPattern 10000 p (.push 106 (.stay 84))) < bonus 128 p) :
    NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 128 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 106 (.stay 84)) + NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 106 (.stay 84)))) + bonus 106 (HazardPattern.afterPattern 10000 p (.push 106 (.stay 84))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 106 (.stay 84)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 106 (.stay 84))) (HazardPattern.afterPattern 10000 p (.push 106 (.stay 84))) < bonus 128 p at decreasing
  rw [gammaAfter446, at128] at decreasing
  have numeric := numeric446 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 106 (.stay 84))) (HazardPattern.afterPattern 10000 p (.push 106 (.stay 84)))
  rw [oldBefore128, at128, literal, oldAfter446, gammaAfter446]
  exact numeric
theorem numeric447 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 128 p
  rw [at128] at beforeRange
  have afterRange := bonus_range 150 (HazardPattern.afterPattern 10000 p (.walk 150))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) ∧ bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) ≤ 2 at afterRange
  rw [gammaAfter447] at afterRange
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
theorem local447 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 150 (HazardPattern.afterPattern 10000 p (.walk 150)) < bonus 128 p) :
    NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 128 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 150) + NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 150))) + bonus 150 (HazardPattern.afterPattern 10000 p (.walk 150)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 150) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) < bonus 128 p at decreasing
  rw [gammaAfter447, at128] at decreasing
  have numeric := numeric447 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150))
  rw [oldBefore128, at128, literal, oldAfter447, gammaAfter447]
  exact numeric
theorem numeric448 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 128 p
  rw [at128] at beforeRange
  have afterRange := bonus_range 150 (HazardPattern.afterPattern 10000 p (.push 150 (.stay 172)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 150 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 150 (.stay 172))) ∧ bonus (HazardPattern.nextHero (.push 150 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 150 (.stay 172))) ≤ 2 at afterRange
  rw [gammaAfter448] at afterRange
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
theorem local448 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 150 (HazardPattern.afterPattern 10000 p (.push 150 (.stay 172))) < bonus 128 p) :
    NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 128 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 150 (.stay 172)) + NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 150 (.stay 172)))) + bonus 150 (HazardPattern.afterPattern 10000 p (.push 150 (.stay 172))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 150 (.stay 172)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 150 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 150 (.stay 172))) < bonus 128 p at decreasing
  rw [gammaAfter448, at128] at decreasing
  have numeric := numeric448 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 150 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 150 (.stay 172)))
  rw [oldBefore128, at128, literal, oldAfter448, gammaAfter448]
  exact numeric
theorem numeric449 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 128 p
  rw [at128] at beforeRange
  have afterRange := bonus_range 127 (HazardPattern.afterPattern 10000 p (.walk 127))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ∧ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ≤ 2 at afterRange
  rw [gammaAfter449] at afterRange
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
theorem local449 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 128 p) :
    NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 128 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 127) + NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) + bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 127) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 128 p at decreasing
  rw [gammaAfter449, at128] at decreasing
  have numeric := numeric449 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127))
  rw [oldBefore128, at128, literal, oldAfter449, gammaAfter449]
  exact numeric
theorem numeric450 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 128 p
  rw [at128] at beforeRange
  have afterRange := bonus_range 127 (HazardPattern.afterPattern 10000 p (.push 127 (.stay 126)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 127 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 126))) ∧ bonus (HazardPattern.nextHero (.push 127 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 126))) ≤ 2 at afterRange
  rw [gammaAfter450] at afterRange
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
theorem local450 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 127 (HazardPattern.afterPattern 10000 p (.push 127 (.stay 126))) < bonus 128 p) :
    NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 128 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 127 (.stay 126)) + NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 127 (.stay 126)))) + bonus 127 (HazardPattern.afterPattern 10000 p (.push 127 (.stay 126))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 127 (.stay 126)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 127 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 126))) < bonus 128 p at decreasing
  rw [gammaAfter450, at128] at decreasing
  have numeric := numeric450 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 127 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 126)))
  rw [oldBefore128, at128, literal, oldAfter450, gammaAfter450]
  exact numeric
theorem numeric451 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 128 p
  rw [at128] at beforeRange
  have afterRange := bonus_range 105 (HazardPattern.afterPattern 10000 p (.walk 105))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ∧ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ≤ 2 at afterRange
  rw [gammaAfter451] at afterRange
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
theorem local451 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 128 p) :
    NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 128 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 105) + NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 105))) + bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 105) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 128 p at decreasing
  rw [gammaAfter451, at128] at decreasing
  have numeric := numeric451 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105))
  rw [oldBefore128, at128, literal, oldAfter451, gammaAfter451]
  exact numeric
theorem numeric452 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 128 p
  rw [at128] at beforeRange
  have afterRange := bonus_range 149 (HazardPattern.afterPattern 10000 p (.walk 149))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ∧ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ≤ 2 at afterRange
  rw [gammaAfter452] at afterRange
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
theorem local452 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 128 p) :
    NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 128 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 149) + NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) + bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 149) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 128 p at decreasing
  rw [gammaAfter452, at128] at decreasing
  have numeric := numeric452 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149))
  rw [oldBefore128, at128, literal, oldAfter452, gammaAfter452]
  exact numeric
theorem numeric453 (p : Pattern) (guard : d82685 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 133 p
  rw [at133] at beforeRange
  have afterRange := bonus_range 111 (HazardPattern.afterPattern 10000 p (.walk 111))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) ∧ bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) ≤ 2 at afterRange
  rw [gammaAfter453] at afterRange
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
theorem local453 (p : Pattern) (guard : d82685 p = 1)
    (decreasing : bonus 111 (HazardPattern.afterPattern 10000 p (.walk 111)) < bonus 133 p) :
    NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 133 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 111) + NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 111))) + bonus 111 (HazardPattern.afterPattern 10000 p (.walk 111)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 111) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) < bonus 133 p at decreasing
  rw [gammaAfter453, at133] at decreasing
  have numeric := numeric453 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111))
  rw [oldBefore133, at133, literal, oldAfter453, gammaAfter453]
  exact numeric
theorem numeric454 (p : Pattern) (guard : d74854 p = 1) (decreasing : d102349 p < d5849 p) :
    d47866 p + d5849 p ≤ (1 : Int) + d47866 p + d102349 p := by
  have beforeRange := bonus_range 133 p
  rw [at133] at beforeRange
  have afterRange := bonus_range 111 (HazardPattern.afterPattern 10000 p (.push 111 (.stay 89)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 111 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 111 (.stay 89))) ∧ bonus (HazardPattern.nextHero (.push 111 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 111 (.stay 89))) ≤ 2 at afterRange
  rw [gammaAfter454] at afterRange
  have possibilities : (d5849 p = 1 ∧ d102349 p = 0) ∨ (d5849 p = 2 ∧ d102349 p = 0) ∨ (d5849 p = 2 ∧ d102349 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro6940 p pair.2
    have combined := andIntro14417 p beforeEq guard
    have complete := andIntro14418 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro6940 p pair.2
    have combined := andIntro6974 p beforeEq guard
    have complete := andIntro14418 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro6941 p pair.2
    have combined := andIntro6974 p beforeEq guard
    have complete := andIntro14419 p combined afterEq
    have bound := compare2 p complete
    omega
theorem local454 (p : Pattern) (guard : d74854 p = 1)
    (decreasing : bonus 111 (HazardPattern.afterPattern 10000 p (.push 111 (.stay 89))) < bonus 133 p) :
    NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 133 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 111 (.stay 89)) + NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 111 (.stay 89)))) + bonus 111 (HazardPattern.afterPattern 10000 p (.push 111 (.stay 89))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 111 (.stay 89)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 111 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 111 (.stay 89))) < bonus 133 p at decreasing
  rw [gammaAfter454, at133] at decreasing
  have numeric := numeric454 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 111 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 111 (.stay 89)))
  rw [oldBefore133, at133, literal, oldAfter454, gammaAfter454]
  exact numeric
theorem numeric455 (p : Pattern) (guard : d102593 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 133 p
  rw [at133] at beforeRange
  have afterRange := bonus_range 155 (HazardPattern.afterPattern 10000 p (.walk 155))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) ∧ bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) ≤ 2 at afterRange
  rw [gammaAfter455] at afterRange
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
theorem local455 (p : Pattern) (guard : d102593 p = 1)
    (decreasing : bonus 155 (HazardPattern.afterPattern 10000 p (.walk 155)) < bonus 133 p) :
    NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 133 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 155) + NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 155))) + bonus 155 (HazardPattern.afterPattern 10000 p (.walk 155)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 155) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) < bonus 133 p at decreasing
  rw [gammaAfter455, at133] at decreasing
  have numeric := numeric455 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155))
  rw [oldBefore133, at133, literal, oldAfter455, gammaAfter455]
  exact numeric
theorem numeric456 (p : Pattern) (guard : d102598 p = 1) (decreasing : d0 p < d5849 p) :
    d47866 p + d5849 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 133 p
  rw [at133] at beforeRange
  have afterRange := bonus_range 155 (HazardPattern.afterPattern 10000 p (.push 155 (.stay 177)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 155 (.stay 177))) (HazardPattern.afterPattern 10000 p (.push 155 (.stay 177))) ∧ bonus (HazardPattern.nextHero (.push 155 (.stay 177))) (HazardPattern.afterPattern 10000 p (.push 155 (.stay 177))) ≤ 2 at afterRange
  rw [gammaAfter456] at afterRange
  have possibilities : (d5849 p = 1 ∧ d0 p = 0) ∨ (d5849 p = 2 ∧ d0 p = 0) ∨ (d5849 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14425 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14429 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14429 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2 p complete
    omega
theorem local456 (p : Pattern) (guard : d102598 p = 1)
    (decreasing : bonus 155 (HazardPattern.afterPattern 10000 p (.push 155 (.stay 177))) < bonus 133 p) :
    NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 133 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 155 (.stay 177)) + NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 155 (.stay 177)))) + bonus 155 (HazardPattern.afterPattern 10000 p (.push 155 (.stay 177))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 155 (.stay 177)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 155 (.stay 177))) (HazardPattern.afterPattern 10000 p (.push 155 (.stay 177))) < bonus 133 p at decreasing
  rw [gammaAfter456, at133] at decreasing
  have numeric := numeric456 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 155 (.stay 177))) (HazardPattern.afterPattern 10000 p (.push 155 (.stay 177)))
  rw [oldBefore133, at133, literal, oldAfter456, gammaAfter456]
  exact numeric
theorem numeric457 (p : Pattern) (guard : d82693 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 133 p
  rw [at133] at beforeRange
  have afterRange := bonus_range 134 (HazardPattern.afterPattern 10000 p (.walk 134))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ∧ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ≤ 2 at afterRange
  rw [gammaAfter457] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro14430 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro14431 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro14431 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local457 (p : Pattern) (guard : d82693 p = 1)
    (decreasing : bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 133 p) :
    NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 133 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 134) + NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 134))) + bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 134) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 133 p at decreasing
  rw [gammaAfter457, at133] at decreasing
  have numeric := numeric457 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134))
  rw [oldBefore133, at133, literal, oldAfter457, gammaAfter457]
  exact numeric
theorem numeric458 (p : Pattern) (guard : d102601 p = 1) (decreasing : d103455 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d103455 p := by
  have beforeRange := bonus_range 133 p
  rw [at133] at beforeRange
  have afterRange := bonus_range 134 (HazardPattern.afterPattern 10000 p (.push 134 (.stay 135)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 134 (.stay 135))) (HazardPattern.afterPattern 10000 p (.push 134 (.stay 135))) ∧ bonus (HazardPattern.nextHero (.push 134 (.stay 135))) (HazardPattern.afterPattern 10000 p (.push 134 (.stay 135))) ≤ 2 at afterRange
  rw [gammaAfter458] at afterRange
  have possibilities : (d5849 p = 1 ∧ d103455 p = 0) ∨ (d5849 p = 2 ∧ d103455 p = 0) ∨ (d5849 p = 2 ∧ d103455 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro7106 p pair.2
    have combined := andIntro14435 p beforeEq guard
    have complete := andIntro14436 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro7106 p pair.2
    have combined := andIntro14440 p beforeEq guard
    have complete := andIntro14436 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro7168 p pair.2
    have combined := andIntro14440 p beforeEq guard
    have complete := andIntro14441 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local458 (p : Pattern) (guard : d102601 p = 1)
    (decreasing : bonus 134 (HazardPattern.afterPattern 10000 p (.push 134 (.stay 135))) < bonus 133 p) :
    NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 133 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 134 (.stay 135)) + NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 134 (.stay 135)))) + bonus 134 (HazardPattern.afterPattern 10000 p (.push 134 (.stay 135))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 134 (.stay 135)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 134 (.stay 135))) (HazardPattern.afterPattern 10000 p (.push 134 (.stay 135))) < bonus 133 p at decreasing
  rw [gammaAfter458, at133] at decreasing
  have numeric := numeric458 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 134 (.stay 135))) (HazardPattern.afterPattern 10000 p (.push 134 (.stay 135)))
  rw [oldBefore133, at133, literal, oldAfter458, gammaAfter458]
  exact numeric
theorem numeric459 (p : Pattern) (guard : d104540 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 133 p
  rw [at133] at beforeRange
  have afterRange := bonus_range 156 (HazardPattern.afterPattern 10000 p (.walk 156))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) ∧ bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) ≤ 2 at afterRange
  rw [gammaAfter459] at afterRange
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
theorem local459 (p : Pattern) (guard : d104540 p = 1)
    (decreasing : bonus 156 (HazardPattern.afterPattern 10000 p (.walk 156)) < bonus 133 p) :
    NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 133 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 156) + NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 156))) + bonus 156 (HazardPattern.afterPattern 10000 p (.walk 156)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 156) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) < bonus 133 p at decreasing
  rw [gammaAfter459, at133] at decreasing
  have numeric := numeric459 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156))
  rw [oldBefore133, at133, literal, oldAfter459, gammaAfter459]
  exact numeric
theorem numeric460 (p : Pattern) (guard : d104541 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 134 p
  rw [at134] at beforeRange
  have afterRange := bonus_range 156 (HazardPattern.afterPattern 10000 p (.walk 156))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) ∧ bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) ≤ 2 at afterRange
  rw [gammaAfter460] at afterRange
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
theorem local460 (p : Pattern) (guard : d104541 p = 1)
    (decreasing : bonus 156 (HazardPattern.afterPattern 10000 p (.walk 156)) < bonus 134 p) :
    NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 134 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 156) + NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 156))) + bonus 156 (HazardPattern.afterPattern 10000 p (.walk 156)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 156) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) < bonus 134 p at decreasing
  rw [gammaAfter460, at134] at decreasing
  have numeric := numeric460 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156))
  rw [oldBefore134, at134, literal, oldAfter460, gammaAfter460]
  exact numeric
theorem numeric461 (p : Pattern) (guard : d104542 p = 1) (decreasing : d8234 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d8234 p := by
  have beforeRange := bonus_range 134 p
  rw [at134] at beforeRange
  have afterRange := bonus_range 135 (HazardPattern.afterPattern 10000 p (.walk 135))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ∧ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ≤ 2 at afterRange
  rw [gammaAfter461] at afterRange
  have possibilities : (d5849 p = 1 ∧ d8234 p = 0) ∨ (d5849 p = 2 ∧ d8234 p = 0) ∨ (d5849 p = 2 ∧ d8234 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro14598 p beforeEq guard
    have complete := andIntro14660 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro14692 p beforeEq guard
    have complete := andIntro14348 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro4924 p pair.2
    have combined := andIntro14692 p beforeEq guard
    have complete := andIntro14392 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local461 (p : Pattern) (guard : d104542 p = 1)
    (decreasing : bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 134 p) :
    NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 134 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 135) + NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 135))) + bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 135) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 134 p at decreasing
  rw [gammaAfter461, at134] at decreasing
  have numeric := numeric461 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135))
  rw [oldBefore134, at134, literal, oldAfter461, gammaAfter461]
  exact numeric
theorem numeric462 (p : Pattern) (guard : d104545 p = 1) (decreasing : d105434 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d105434 p := by
  have beforeRange := bonus_range 134 p
  rw [at134] at beforeRange
  have afterRange := bonus_range 135 (HazardPattern.afterPattern 10000 p (.push 135 (.stay 136)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 135 (.stay 136))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 136))) ∧ bonus (HazardPattern.nextHero (.push 135 (.stay 136))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 136))) ≤ 2 at afterRange
  rw [gammaAfter462] at afterRange
  have possibilities : (d5849 p = 1 ∧ d105434 p = 0) ∨ (d5849 p = 2 ∧ d105434 p = 0) ∨ (d5849 p = 2 ∧ d105434 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro7347 p pair.2
    have combined := andIntro14948 p beforeEq guard
    have complete := andIntro15139 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro7347 p pair.2
    have combined := andIntro15172 p beforeEq guard
    have complete := andIntro15216 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro7421 p pair.2
    have combined := andIntro15172 p beforeEq guard
    have complete := andIntro15260 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local462 (p : Pattern) (guard : d104545 p = 1)
    (decreasing : bonus 135 (HazardPattern.afterPattern 10000 p (.push 135 (.stay 136))) < bonus 134 p) :
    NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 134 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 135 (.stay 136)) + NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 135 (.stay 136)))) + bonus 135 (HazardPattern.afterPattern 10000 p (.push 135 (.stay 136))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 135 (.stay 136)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 135 (.stay 136))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 136))) < bonus 134 p at decreasing
  rw [gammaAfter462, at134] at decreasing
  have numeric := numeric462 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 135 (.stay 136))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 136)))
  rw [oldBefore134, at134, literal, oldAfter462, gammaAfter462]
  exact numeric
theorem numeric463 (p : Pattern) (guard : d82693 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 134 p
  rw [at134] at beforeRange
  have afterRange := bonus_range 133 (HazardPattern.afterPattern 10000 p (.walk 133))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) ∧ bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) ≤ 2 at afterRange
  rw [gammaAfter463] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro14430 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro14431 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro14431 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local463 (p : Pattern) (guard : d82693 p = 1)
    (decreasing : bonus 133 (HazardPattern.afterPattern 10000 p (.walk 133)) < bonus 134 p) :
    NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 134 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 133) + NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 133))) + bonus 133 (HazardPattern.afterPattern 10000 p (.walk 133)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 133) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) < bonus 134 p at decreasing
  rw [gammaAfter463, at134] at decreasing
  have numeric := numeric463 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133))
  rw [oldBefore134, at134, literal, oldAfter463, gammaAfter463]
  exact numeric
theorem numeric464 (p : Pattern) (guard : d94517 p = 1) (decreasing : d6737 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d6737 p := by
  have beforeRange := bonus_range 134 p
  rw [at134] at beforeRange
  have afterRange := bonus_range 113 (HazardPattern.afterPattern 10000 p (.walk 113))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) ∧ bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) ≤ 2 at afterRange
  rw [gammaAfter464] at afterRange
  have possibilities : (d5849 p = 1 ∧ d6737 p = 0) ∨ (d5849 p = 2 ∧ d6737 p = 0) ∨ (d5849 p = 2 ∧ d6737 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3730 p pair.2
    have combined := andIntro15399 p beforeEq guard
    have complete := andIntro15545 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3730 p pair.2
    have combined := andIntro15577 p beforeEq guard
    have complete := andIntro15621 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3797 p pair.2
    have combined := andIntro15577 p beforeEq guard
    have complete := andIntro15665 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local464 (p : Pattern) (guard : d94517 p = 1)
    (decreasing : bonus 113 (HazardPattern.afterPattern 10000 p (.walk 113)) < bonus 134 p) :
    NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 134 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 113) + NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 113))) + bonus 113 (HazardPattern.afterPattern 10000 p (.walk 113)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 113) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) < bonus 134 p at decreasing
  rw [gammaAfter464, at134] at decreasing
  have numeric := numeric464 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113))
  rw [oldBefore134, at134, literal, oldAfter464, gammaAfter464]
  exact numeric
theorem numeric465 (p : Pattern) (guard : d82694 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 134 p
  rw [at134] at beforeRange
  have afterRange := bonus_range 111 (HazardPattern.afterPattern 10000 p (.walk 111))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) ∧ bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) ≤ 2 at afterRange
  rw [gammaAfter465] at afterRange
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
theorem local465 (p : Pattern) (guard : d82694 p = 1)
    (decreasing : bonus 111 (HazardPattern.afterPattern 10000 p (.walk 111)) < bonus 134 p) :
    NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 134 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 111) + NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 111))) + bonus 111 (HazardPattern.afterPattern 10000 p (.walk 111)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 111) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) < bonus 134 p at decreasing
  rw [gammaAfter465, at134] at decreasing
  have numeric := numeric465 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111))
  rw [oldBefore134, at134, literal, oldAfter465, gammaAfter465]
  exact numeric
theorem numeric466 (p : Pattern) (guard : d107485 p = 1) (decreasing : d12224 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d12224 p := by
  have beforeRange := bonus_range 134 p
  rw [at134] at beforeRange
  have afterRange := bonus_range 157 (HazardPattern.afterPattern 10000 p (.walk 157))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) ∧ bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) ≤ 2 at afterRange
  rw [gammaAfter466] at afterRange
  have possibilities : (d5849 p = 1 ∧ d12224 p = 0) ∨ (d5849 p = 2 ∧ d12224 p = 0) ∨ (d5849 p = 2 ∧ d12224 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro7713 p pair.2
    have combined := andIntro15902 p beforeEq guard
    have complete := andIntro16139 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro7713 p pair.2
    have combined := andIntro16171 p beforeEq guard
    have complete := andIntro16220 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro7817 p pair.2
    have combined := andIntro16171 p beforeEq guard
    have complete := andIntro16269 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local466 (p : Pattern) (guard : d107485 p = 1)
    (decreasing : bonus 157 (HazardPattern.afterPattern 10000 p (.walk 157)) < bonus 134 p) :
    NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 134 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 157) + NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 157))) + bonus 157 (HazardPattern.afterPattern 10000 p (.walk 157)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 157) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) < bonus 134 p at decreasing
  rw [gammaAfter466, at134] at decreasing
  have numeric := numeric466 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157))
  rw [oldBefore134, at134, literal, oldAfter466, gammaAfter466]
  exact numeric
theorem numeric467 (p : Pattern) (guard : d109328 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 134 p
  rw [at134] at beforeRange
  have afterRange := bonus_range 155 (HazardPattern.afterPattern 10000 p (.walk 155))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) ∧ bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) ≤ 2 at afterRange
  rw [gammaAfter467] at afterRange
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
theorem local467 (p : Pattern) (guard : d109328 p = 1)
    (decreasing : bonus 155 (HazardPattern.afterPattern 10000 p (.walk 155)) < bonus 134 p) :
    NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 134 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 155) + NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 155))) + bonus 155 (HazardPattern.afterPattern 10000 p (.walk 155)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 155) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) < bonus 134 p at decreasing
  rw [gammaAfter467, at134] at decreasing
  have numeric := numeric467 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155))
  rw [oldBefore134, at134, literal, oldAfter467, gammaAfter467]
  exact numeric
theorem numeric468 (p : Pattern) (guard : d83662 p = 1) (decreasing : d6737 p < d8234 p) :
    d47866 p + d8234 p ≤ (0 : Int) + d47866 p + d6737 p := by
  have beforeRange := bonus_range 135 p
  rw [at135] at beforeRange
  have afterRange := bonus_range 113 (HazardPattern.afterPattern 10000 p (.walk 113))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) ∧ bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) ≤ 2 at afterRange
  rw [gammaAfter468] at afterRange
  have possibilities : (d8234 p = 1 ∧ d6737 p = 0) ∨ (d8234 p = 2 ∧ d6737 p = 0) ∨ (d8234 p = 2 ∧ d6737 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4924 p pair.1
    have afterEq := eqIntro3730 p pair.2
    have combined := andIntro16398 p guard beforeEq
    have complete := andIntro15545 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro3730 p pair.2
    have combined := andIntro16430 p guard beforeEq
    have complete := andIntro15621 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro3797 p pair.2
    have combined := andIntro16430 p guard beforeEq
    have complete := andIntro15665 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local468 (p : Pattern) (guard : d83662 p = 1)
    (decreasing : bonus 113 (HazardPattern.afterPattern 10000 p (.walk 113)) < bonus 135 p) :
    NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 135 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 113) + NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 113))) + bonus 113 (HazardPattern.afterPattern 10000 p (.walk 113)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 113) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) < bonus 135 p at decreasing
  rw [gammaAfter468, at135] at decreasing
  have numeric := numeric468 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113))
  rw [oldBefore135, at135, literal, oldAfter468, gammaAfter468]
  exact numeric
theorem numeric469 (p : Pattern) (guard : d77845 p = 1) (decreasing : d109664 p < d8234 p) :
    d47866 p + d8234 p ≤ (2 : Int) + d47866 p + d109664 p := by
  have beforeRange := bonus_range 135 p
  rw [at135] at beforeRange
  have afterRange := bonus_range 113 (HazardPattern.afterPattern 10000 p (.push 113 (.stay 91)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 113 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 113 (.stay 91))) ∧ bonus (HazardPattern.nextHero (.push 113 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 113 (.stay 91))) ≤ 2 at afterRange
  rw [gammaAfter469] at afterRange
  have possibilities : (d8234 p = 1 ∧ d109664 p = 0) ∨ (d8234 p = 2 ∧ d109664 p = 0) ∨ (d8234 p = 2 ∧ d109664 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4924 p pair.1
    have afterEq := eqIntro8079 p pair.2
    have combined := andIntro16570 p guard beforeEq
    have complete := andIntro16692 p afterEq combined
    have bound := compare10066 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro8079 p pair.2
    have combined := andIntro16729 p guard beforeEq
    have complete := andIntro16778 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro8123 p pair.2
    have combined := andIntro16729 p guard beforeEq
    have complete := andIntro16822 p combined afterEq
    have bound := compare10066 p complete
    omega
theorem local469 (p : Pattern) (guard : d77845 p = 1)
    (decreasing : bonus 113 (HazardPattern.afterPattern 10000 p (.push 113 (.stay 91))) < bonus 135 p) :
    NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 135 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 113 (.stay 91)) + NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 113 (.stay 91)))) + bonus 113 (HazardPattern.afterPattern 10000 p (.push 113 (.stay 91))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 113 (.stay 91)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 113 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 113 (.stay 91))) < bonus 135 p at decreasing
  rw [gammaAfter469, at135] at decreasing
  have numeric := numeric469 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 113 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 113 (.stay 91)))
  rw [oldBefore135, at135, literal, oldAfter469, gammaAfter469]
  exact numeric
theorem numeric470 (p : Pattern) (guard : d107483 p = 1) (decreasing : d12224 p < d8234 p) :
    d47866 p + d8234 p ≤ (0 : Int) + d47866 p + d12224 p := by
  have beforeRange := bonus_range 135 p
  rw [at135] at beforeRange
  have afterRange := bonus_range 157 (HazardPattern.afterPattern 10000 p (.walk 157))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) ∧ bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) ≤ 2 at afterRange
  rw [gammaAfter470] at afterRange
  have possibilities : (d8234 p = 1 ∧ d12224 p = 0) ∨ (d8234 p = 2 ∧ d12224 p = 0) ∨ (d8234 p = 2 ∧ d12224 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4924 p pair.1
    have afterEq := eqIntro7713 p pair.2
    have combined := andIntro17049 p beforeEq guard
    have complete := andIntro17226 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro7713 p pair.2
    have combined := andIntro17258 p beforeEq guard
    have complete := andIntro17302 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro7817 p pair.2
    have combined := andIntro17258 p beforeEq guard
    have complete := andIntro17346 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local470 (p : Pattern) (guard : d107483 p = 1)
    (decreasing : bonus 157 (HazardPattern.afterPattern 10000 p (.walk 157)) < bonus 135 p) :
    NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 135 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 157) + NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 157))) + bonus 157 (HazardPattern.afterPattern 10000 p (.walk 157)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 157) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) < bonus 135 p at decreasing
  rw [gammaAfter470, at135] at decreasing
  have numeric := numeric470 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157))
  rw [oldBefore135, at135, literal, oldAfter470, gammaAfter470]
  exact numeric
theorem numeric471 (p : Pattern) (guard : d92315 p = 1) (decreasing : d9291 p < d8234 p) :
    d47866 p + d8234 p ≤ (0 : Int) + d47866 p + d9291 p := by
  have beforeRange := bonus_range 135 p
  rw [at135] at beforeRange
  have afterRange := bonus_range 136 (HazardPattern.afterPattern 10000 p (.walk 136))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ∧ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ≤ 2 at afterRange
  rw [gammaAfter471] at afterRange
  have possibilities : (d8234 p = 1 ∧ d9291 p = 0) ∨ (d8234 p = 2 ∧ d9291 p = 0) ∨ (d8234 p = 2 ∧ d9291 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4924 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro17513 p beforeEq guard
    have complete := andIntro17700 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro17732 p guard beforeEq
    have complete := andIntro17781 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro5906 p pair.2
    have combined := andIntro17732 p guard beforeEq
    have complete := andIntro17825 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local471 (p : Pattern) (guard : d92315 p = 1)
    (decreasing : bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 135 p) :
    NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 135 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 136) + NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 136))) + bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 136) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 135 p at decreasing
  rw [gammaAfter471, at135] at decreasing
  have numeric := numeric471 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136))
  rw [oldBefore135, at135, literal, oldAfter471, gammaAfter471]
  exact numeric
theorem numeric472 (p : Pattern) (guard : d104542 p = 1) (decreasing : d5849 p < d8234 p) :
    d47866 p + d8234 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 135 p
  rw [at135] at beforeRange
  have afterRange := bonus_range 134 (HazardPattern.afterPattern 10000 p (.walk 134))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ∧ bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) ≤ 2 at afterRange
  rw [gammaAfter472] at afterRange
  have possibilities : (d8234 p = 1 ∧ d5849 p = 0) ∨ (d8234 p = 2 ∧ d5849 p = 0) ∨ (d8234 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4924 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro17826 p beforeEq guard
    have complete := andIntro17953 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro17954 p beforeEq guard
    have complete := andIntro17998 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro17954 p beforeEq guard
    have complete := andIntro18042 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local472 (p : Pattern) (guard : d104542 p = 1)
    (decreasing : bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 135 p) :
    NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 135 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 134) + NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 134))) + bonus 134 (HazardPattern.afterPattern 10000 p (.walk 134)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 134) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) < bonus 135 p at decreasing
  rw [gammaAfter472, at135] at decreasing
  have numeric := numeric472 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134))
  rw [oldBefore135, at135, literal, oldAfter472, gammaAfter472]
  exact numeric
theorem numeric473 (p : Pattern) (guard : d102601 p = 1) (decreasing : d0 p < d8234 p) :
    d47866 p + d8234 p ≤ (2 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 135 p
  rw [at135] at beforeRange
  have afterRange := bonus_range 134 (HazardPattern.afterPattern 10000 p (.push 134 (.stay 133)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 134 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 134 (.stay 133))) ∧ bonus (HazardPattern.nextHero (.push 134 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 134 (.stay 133))) ≤ 2 at afterRange
  rw [gammaAfter473] at afterRange
  have possibilities : (d8234 p = 1 ∧ d0 p = 0) ∨ (d8234 p = 2 ∧ d0 p = 0) ∨ (d8234 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4924 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro18046 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10066 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro18050 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro18050 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10066 p complete
    omega
theorem local473 (p : Pattern) (guard : d102601 p = 1)
    (decreasing : bonus 134 (HazardPattern.afterPattern 10000 p (.push 134 (.stay 133))) < bonus 135 p) :
    NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 135 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 134 (.stay 133)) + NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 134 (.stay 133)))) + bonus 134 (HazardPattern.afterPattern 10000 p (.push 134 (.stay 133))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 134 (.stay 133)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 134 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 134 (.stay 133))) < bonus 135 p at decreasing
  rw [gammaAfter473, at135] at decreasing
  have numeric := numeric473 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 134 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 134 (.stay 133)))
  rw [oldBefore135, at135, literal, oldAfter473, gammaAfter473]
  exact numeric
theorem numeric474 (p : Pattern) (guard : d98801 p = 1) (decreasing : d7239 p < d8234 p) :
    d47866 p + d8234 p ≤ (0 : Int) + d47866 p + d7239 p := by
  have beforeRange := bonus_range 135 p
  rw [at135] at beforeRange
  have afterRange := bonus_range 114 (HazardPattern.afterPattern 10000 p (.walk 114))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) ∧ bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) ≤ 2 at afterRange
  rw [gammaAfter474] at afterRange
  have possibilities : (d8234 p = 1 ∧ d7239 p = 0) ∨ (d8234 p = 2 ∧ d7239 p = 0) ∨ (d8234 p = 2 ∧ d7239 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4924 p pair.1
    have afterEq := eqIntro4312 p pair.2
    have combined := andIntro18112 p beforeEq guard
    have complete := andIntro18194 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro4312 p pair.2
    have combined := andIntro18195 p guard beforeEq
    have complete := andIntro18239 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro4356 p pair.2
    have combined := andIntro18195 p guard beforeEq
    have complete := andIntro18283 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local474 (p : Pattern) (guard : d98801 p = 1)
    (decreasing : bonus 114 (HazardPattern.afterPattern 10000 p (.walk 114)) < bonus 135 p) :
    NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 135 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 114) + NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 114))) + bonus 114 (HazardPattern.afterPattern 10000 p (.walk 114)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 114) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) < bonus 135 p at decreasing
  rw [gammaAfter474, at135] at decreasing
  have numeric := numeric474 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114))
  rw [oldBefore135, at135, literal, oldAfter474, gammaAfter474]
  exact numeric
theorem numeric475 (p : Pattern) (guard : d112688 p = 1) (decreasing : d13979 p < d8234 p) :
    d47866 p + d8234 p ≤ (0 : Int) + d47866 p + d13979 p := by
  have beforeRange := bonus_range 135 p
  rw [at135] at beforeRange
  have afterRange := bonus_range 158 (HazardPattern.afterPattern 10000 p (.walk 158))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) ∧ bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) ≤ 2 at afterRange
  rw [gammaAfter475] at afterRange
  have possibilities : (d8234 p = 1 ∧ d13979 p = 0) ∨ (d8234 p = 2 ∧ d13979 p = 0) ∨ (d8234 p = 2 ∧ d13979 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4924 p pair.1
    have afterEq := eqIntro8488 p pair.2
    have combined := andIntro18520 p beforeEq guard
    have complete := andIntro18785 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro8488 p pair.2
    have combined := andIntro18817 p beforeEq guard
    have complete := andIntro18869 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro8624 p pair.2
    have combined := andIntro18817 p beforeEq guard
    have complete := andIntro18918 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local475 (p : Pattern) (guard : d112688 p = 1)
    (decreasing : bonus 158 (HazardPattern.afterPattern 10000 p (.walk 158)) < bonus 135 p) :
    NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 135 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 158) + NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 158))) + bonus 158 (HazardPattern.afterPattern 10000 p (.walk 158)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 158) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) < bonus 135 p at decreasing
  rw [gammaAfter475, at135] at decreasing
  have numeric := numeric475 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158))
  rw [oldBefore135, at135, literal, oldAfter475, gammaAfter475]
  exact numeric
theorem numeric476 (p : Pattern) (guard : d115573 p = 1) (decreasing : d5849 p < d8234 p) :
    d47866 p + d8234 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 135 p
  rw [at135] at beforeRange
  have afterRange := bonus_range 156 (HazardPattern.afterPattern 10000 p (.walk 156))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) ∧ bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) ≤ 2 at afterRange
  rw [gammaAfter476] at afterRange
  have possibilities : (d8234 p = 1 ∧ d5849 p = 0) ∨ (d8234 p = 2 ∧ d5849 p = 0) ∨ (d8234 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro4924 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro18919 p beforeEq guard
    have complete := andIntro17953 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro18920 p beforeEq guard
    have complete := andIntro17998 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8014 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro18920 p beforeEq guard
    have complete := andIntro18042 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local476 (p : Pattern) (guard : d115573 p = 1)
    (decreasing : bonus 156 (HazardPattern.afterPattern 10000 p (.walk 156)) < bonus 135 p) :
    NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 135 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 156) + NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 156))) + bonus 156 (HazardPattern.afterPattern 10000 p (.walk 156)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 156) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) < bonus 135 p at decreasing
  rw [gammaAfter476, at135] at decreasing
  have numeric := numeric476 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156))
  rw [oldBefore135, at135, literal, oldAfter476, gammaAfter476]
  exact numeric
theorem numeric477 (p : Pattern) (guard : d94518 p = 1) (decreasing : d7239 p < d9291 p) :
    d47866 p + d9291 p ≤ (0 : Int) + d47866 p + d7239 p := by
  have beforeRange := bonus_range 136 p
  rw [at136] at beforeRange
  have afterRange := bonus_range 114 (HazardPattern.afterPattern 10000 p (.walk 114))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) ∧ bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) ≤ 2 at afterRange
  rw [gammaAfter477] at afterRange
  have possibilities : (d9291 p = 1 ∧ d7239 p = 0) ∨ (d9291 p = 2 ∧ d7239 p = 0) ∨ (d9291 p = 2 ∧ d7239 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro5906 p pair.1
    have afterEq := eqIntro4312 p pair.2
    have combined := andIntro18921 p beforeEq guard
    have complete := andIntro19110 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro4312 p pair.2
    have combined := andIntro19111 p guard beforeEq
    have complete := andIntro19160 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro4356 p pair.2
    have combined := andIntro19111 p guard beforeEq
    have complete := andIntro19204 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local477 (p : Pattern) (guard : d94518 p = 1)
    (decreasing : bonus 114 (HazardPattern.afterPattern 10000 p (.walk 114)) < bonus 136 p) :
    NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 136 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 114) + NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 114))) + bonus 114 (HazardPattern.afterPattern 10000 p (.walk 114)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 114) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) < bonus 136 p at decreasing
  rw [gammaAfter477, at136] at decreasing
  have numeric := numeric477 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114))
  rw [oldBefore136, at136, literal, oldAfter477, gammaAfter477]
  exact numeric
theorem numeric478 (p : Pattern) (guard : d115574 p = 1) (decreasing : d13979 p < d9291 p) :
    d47866 p + d9291 p ≤ (0 : Int) + d47866 p + d13979 p := by
  have beforeRange := bonus_range 136 p
  rw [at136] at beforeRange
  have afterRange := bonus_range 158 (HazardPattern.afterPattern 10000 p (.walk 158))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) ∧ bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) ≤ 2 at afterRange
  rw [gammaAfter478] at afterRange
  have possibilities : (d9291 p = 1 ∧ d13979 p = 0) ∨ (d9291 p = 2 ∧ d13979 p = 0) ∨ (d9291 p = 2 ∧ d13979 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro5906 p pair.1
    have afterEq := eqIntro8488 p pair.2
    have combined := andIntro19451 p beforeEq guard
    have complete := andIntro19632 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro8488 p pair.2
    have combined := andIntro19669 p beforeEq guard
    have complete := andIntro19716 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro8624 p pair.2
    have combined := andIntro19669 p beforeEq guard
    have complete := andIntro19760 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local478 (p : Pattern) (guard : d115574 p = 1)
    (decreasing : bonus 158 (HazardPattern.afterPattern 10000 p (.walk 158)) < bonus 136 p) :
    NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 136 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 158) + NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 158))) + bonus 158 (HazardPattern.afterPattern 10000 p (.walk 158)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 158) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) < bonus 136 p at decreasing
  rw [gammaAfter478, at136] at decreasing
  have numeric := numeric478 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158))
  rw [oldBefore136, at136, literal, oldAfter478, gammaAfter478]
  exact numeric
theorem numeric479 (p : Pattern) (guard : d116753 p = 1) (decreasing : d118614 p < d9291 p) :
    d47866 p + d9291 p ≤ (0 : Int) + d47866 p + d118614 p := by
  have beforeRange := bonus_range 136 p
  rw [at136] at beforeRange
  have afterRange := bonus_range 158 (HazardPattern.afterPattern 10000 p (.push 158 (.stay 180)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 158 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 180))) ∧ bonus (HazardPattern.nextHero (.push 158 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 180))) ≤ 2 at afterRange
  rw [gammaAfter479] at afterRange
  have possibilities : (d9291 p = 1 ∧ d118614 p = 0) ∨ (d9291 p = 2 ∧ d118614 p = 0) ∨ (d9291 p = 2 ∧ d118614 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro5906 p pair.1
    have afterEq := eqIntro9207 p pair.2
    have combined := andIntro20094 p beforeEq guard
    have complete := andIntro20376 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro9207 p pair.2
    have combined := andIntro20414 p beforeEq guard
    have complete := andIntro20462 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro9345 p pair.2
    have combined := andIntro20414 p beforeEq guard
    have complete := andIntro20506 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local479 (p : Pattern) (guard : d116753 p = 1)
    (decreasing : bonus 158 (HazardPattern.afterPattern 10000 p (.push 158 (.stay 180))) < bonus 136 p) :
    NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 136 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 158 (.stay 180)) + NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 158 (.stay 180)))) + bonus 158 (HazardPattern.afterPattern 10000 p (.push 158 (.stay 180))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 158 (.stay 180)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 158 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 180))) < bonus 136 p at decreasing
  rw [gammaAfter479, at136] at decreasing
  have numeric := numeric479 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 158 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 180)))
  rw [oldBefore136, at136, literal, oldAfter479, gammaAfter479]
  exact numeric
theorem numeric480 (p : Pattern) (guard : d92315 p = 1) (decreasing : d8234 p < d9291 p) :
    d47866 p + d9291 p ≤ (0 : Int) + d47866 p + d8234 p := by
  have beforeRange := bonus_range 136 p
  rw [at136] at beforeRange
  have afterRange := bonus_range 135 (HazardPattern.afterPattern 10000 p (.walk 135))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ∧ bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) ≤ 2 at afterRange
  rw [gammaAfter480] at afterRange
  have possibilities : (d9291 p = 1 ∧ d8234 p = 0) ∨ (d9291 p = 2 ∧ d8234 p = 0) ∨ (d9291 p = 2 ∧ d8234 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro5906 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro20681 p guard beforeEq
    have complete := andIntro20836 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro4845 p pair.2
    have combined := andIntro20873 p guard beforeEq
    have complete := andIntro20917 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro4924 p pair.2
    have combined := andIntro20873 p guard beforeEq
    have complete := andIntro20961 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local480 (p : Pattern) (guard : d92315 p = 1)
    (decreasing : bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 136 p) :
    NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 136 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 135) + NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 135))) + bonus 135 (HazardPattern.afterPattern 10000 p (.walk 135)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 135) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) < bonus 136 p at decreasing
  rw [gammaAfter480, at136] at decreasing
  have numeric := numeric480 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135))
  rw [oldBefore136, at136, literal, oldAfter480, gammaAfter480]
  exact numeric
theorem numeric481 (p : Pattern) (guard : d104545 p = 1) (decreasing : d0 p < d9291 p) :
    d47866 p + d9291 p ≤ (2 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 136 p
  rw [at136] at beforeRange
  have afterRange := bonus_range 135 (HazardPattern.afterPattern 10000 p (.push 135 (.stay 134)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 135 (.stay 134))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 134))) ∧ bonus (HazardPattern.nextHero (.push 135 (.stay 134))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 134))) ≤ 2 at afterRange
  rw [gammaAfter481] at afterRange
  have possibilities : (d9291 p = 1 ∧ d0 p = 0) ∨ (d9291 p = 2 ∧ d0 p = 0) ∨ (d9291 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro5906 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro21148 p beforeEq guard
    have complete := andIntro21149 p afterEq combined
    have bound := compare10067 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro21186 p beforeEq guard
    have complete := andIntro21187 p afterEq combined
    have bound := compare10068 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro21186 p beforeEq guard
    have complete := andIntro21188 p afterEq combined
    have bound := compare10066 p complete
    omega
theorem local481 (p : Pattern) (guard : d104545 p = 1)
    (decreasing : bonus 135 (HazardPattern.afterPattern 10000 p (.push 135 (.stay 134))) < bonus 136 p) :
    NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 136 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 135 (.stay 134)) + NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 135 (.stay 134)))) + bonus 135 (HazardPattern.afterPattern 10000 p (.push 135 (.stay 134))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 135 (.stay 134)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 135 (.stay 134))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 134))) < bonus 136 p at decreasing
  rw [gammaAfter481, at136] at decreasing
  have numeric := numeric481 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 135 (.stay 134))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 134)))
  rw [oldBefore136, at136, literal, oldAfter481, gammaAfter481]
  exact numeric
theorem numeric482 (p : Pattern) (guard : d100902 p = 1) (decreasing : d0 p < d9291 p) :
    d47866 p + d9291 p ≤ (0 : Int) + d48097 p + d0 p := by
  have beforeRange := bonus_range 136 p
  rw [at136] at beforeRange
  have afterRange := bonus_range 115 (HazardPattern.afterPattern 10000 p (.walk 115))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) ∧ bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) ≤ 2 at afterRange
  rw [gammaAfter482] at afterRange
  have possibilities : (d9291 p = 1 ∧ d0 p = 0) ∨ (d9291 p = 2 ∧ d0 p = 0) ∨ (d9291 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro5906 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro21410 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4397 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro21448 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4398 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro21448 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4397 p complete
    omega
theorem local482 (p : Pattern) (guard : d100902 p = 1)
    (decreasing : bonus 115 (HazardPattern.afterPattern 10000 p (.walk 115)) < bonus 136 p) :
    NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 136 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 115) + NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 115))) + bonus 115 (HazardPattern.afterPattern 10000 p (.walk 115)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 115) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) < bonus 136 p at decreasing
  rw [gammaAfter482, at136] at decreasing
  have numeric := numeric482 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115))
  rw [oldBefore136, at136, literal, oldAfter482, gammaAfter482]
  exact numeric
theorem numeric483 (p : Pattern) (guard : d92317 p = 1) (decreasing : d6737 p < d9291 p) :
    d47866 p + d9291 p ≤ (0 : Int) + d47866 p + d6737 p := by
  have beforeRange := bonus_range 136 p
  rw [at136] at beforeRange
  have afterRange := bonus_range 113 (HazardPattern.afterPattern 10000 p (.walk 113))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) ∧ bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) ≤ 2 at afterRange
  rw [gammaAfter483] at afterRange
  have possibilities : (d9291 p = 1 ∧ d6737 p = 0) ∨ (d9291 p = 2 ∧ d6737 p = 0) ∨ (d9291 p = 2 ∧ d6737 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro5906 p pair.1
    have afterEq := eqIntro3730 p pair.2
    have combined := andIntro21585 p guard beforeEq
    have complete := andIntro21709 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro3730 p pair.2
    have combined := andIntro21746 p guard beforeEq
    have complete := andIntro21790 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro3797 p pair.2
    have combined := andIntro21746 p guard beforeEq
    have complete := andIntro21834 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local483 (p : Pattern) (guard : d92317 p = 1)
    (decreasing : bonus 113 (HazardPattern.afterPattern 10000 p (.walk 113)) < bonus 136 p) :
    NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 136 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 113) + NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 113))) + bonus 113 (HazardPattern.afterPattern 10000 p (.walk 113)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 113) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) < bonus 136 p at decreasing
  rw [gammaAfter483, at136] at decreasing
  have numeric := numeric483 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113))
  rw [oldBefore136, at136, literal, oldAfter483, gammaAfter483]
  exact numeric
theorem numeric484 (p : Pattern) (guard : d122306 p = 1) (decreasing : d15965 p < d9291 p) :
    d47866 p + d9291 p ≤ (0 : Int) + d47866 p + d15965 p := by
  have beforeRange := bonus_range 136 p
  rw [at136] at beforeRange
  have afterRange := bonus_range 159 (HazardPattern.afterPattern 10000 p (.walk 159))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ∧ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ≤ 2 at afterRange
  rw [gammaAfter484] at afterRange
  have possibilities : (d9291 p = 1 ∧ d15965 p = 0) ∨ (d9291 p = 2 ∧ d15965 p = 0) ∨ (d9291 p = 2 ∧ d15965 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro5906 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro22127 p beforeEq guard
    have complete := andIntro22411 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro22448 p beforeEq guard
    have complete := andIntro22503 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro9862 p pair.2
    have combined := andIntro22448 p beforeEq guard
    have complete := andIntro22552 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local484 (p : Pattern) (guard : d122306 p = 1)
    (decreasing : bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 136 p) :
    NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 136 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 159) + NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 159))) + bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 159) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 136 p at decreasing
  rw [gammaAfter484, at136] at decreasing
  have numeric := numeric484 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159))
  rw [oldBefore136, at136, literal, oldAfter484, gammaAfter484]
  exact numeric
theorem numeric485 (p : Pattern) (guard : d125748 p = 1) (decreasing : d12224 p < d9291 p) :
    d47866 p + d9291 p ≤ (0 : Int) + d47866 p + d12224 p := by
  have beforeRange := bonus_range 136 p
  rw [at136] at beforeRange
  have afterRange := bonus_range 157 (HazardPattern.afterPattern 10000 p (.walk 157))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) ∧ bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) ≤ 2 at afterRange
  rw [gammaAfter485] at afterRange
  have possibilities : (d9291 p = 1 ∧ d12224 p = 0) ∨ (d9291 p = 2 ∧ d12224 p = 0) ∨ (d9291 p = 2 ∧ d12224 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro5906 p pair.1
    have afterEq := eqIntro7713 p pair.2
    have combined := andIntro22799 p beforeEq guard
    have complete := andIntro22994 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro7713 p pair.2
    have combined := andIntro23031 p beforeEq guard
    have complete := andIntro23075 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro8829 p pair.1
    have afterEq := eqIntro7817 p pair.2
    have combined := andIntro23031 p beforeEq guard
    have complete := andIntro23119 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local485 (p : Pattern) (guard : d125748 p = 1)
    (decreasing : bonus 157 (HazardPattern.afterPattern 10000 p (.walk 157)) < bonus 136 p) :
    NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 136 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 157) + NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 157))) + bonus 157 (HazardPattern.afterPattern 10000 p (.walk 157)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 157) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) < bonus 136 p at decreasing
  rw [gammaAfter485, at136] at decreasing
  have numeric := numeric485 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157))
  rw [oldBefore136, at136, literal, oldAfter485, gammaAfter485]
  exact numeric
theorem numeric486 (p : Pattern) (guard : d100899 p = 1) (decreasing : d0 p < d0 p) :
    d48251 p + d0 p ≤ (0 : Int) + d48115 p + d0 p := by
  have beforeRange := bonus_range 138 p
  rw [at138] at beforeRange
  have afterRange := bonus_range 116 (HazardPattern.afterPattern 10000 p (.walk 116))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) ∧ bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) ≤ 2 at afterRange
  rw [gammaAfter486] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14403 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10069 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14403 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10070 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14403 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10069 p complete
    omega
theorem local486 (p : Pattern) (guard : d100899 p = 1)
    (decreasing : bonus 116 (HazardPattern.afterPattern 10000 p (.walk 116)) < bonus 138 p) :
    NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 138 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 116) + NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 116))) + bonus 116 (HazardPattern.afterPattern 10000 p (.walk 116)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 116) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) < bonus 138 p at decreasing
  rw [gammaAfter486, at138] at decreasing
  have numeric := numeric486 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116))
  rw [oldBefore138, at138, literal, oldAfter486, gammaAfter486]
  exact numeric
theorem numeric487 (p : Pattern) (guard : d82340 p = 1) (decreasing : d0 p < d0 p) :
    d48251 p + d0 p ≤ (4 : Int) + d126872 p + d0 p := by
  have beforeRange := bonus_range 138 p
  rw [at138] at beforeRange
  have afterRange := bonus_range 116 (HazardPattern.afterPattern 10000 p (.push 116 (.stay 94)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 116 (.stay 94))) (HazardPattern.afterPattern 10000 p (.push 116 (.stay 94))) ∧ bonus (HazardPattern.nextHero (.push 116 (.stay 94))) (HazardPattern.afterPattern 10000 p (.push 116 (.stay 94))) ≤ 2 at afterRange
  rw [gammaAfter487] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9135 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10071 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9135 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10072 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9135 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10071 p complete
    omega
theorem local487 (p : Pattern) (guard : d82340 p = 1)
    (decreasing : bonus 116 (HazardPattern.afterPattern 10000 p (.push 116 (.stay 94))) < bonus 138 p) :
    NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 138 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 116 (.stay 94)) + NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 116 (.stay 94)))) + bonus 116 (HazardPattern.afterPattern 10000 p (.push 116 (.stay 94))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 116 (.stay 94)) = (4 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 116 (.stay 94))) (HazardPattern.afterPattern 10000 p (.push 116 (.stay 94))) < bonus 138 p at decreasing
  rw [gammaAfter487, at138] at decreasing
  have numeric := numeric487 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 116 (.stay 94))) (HazardPattern.afterPattern 10000 p (.push 116 (.stay 94)))
  rw [oldBefore138, at138, literal, oldAfter487, gammaAfter487]
  exact numeric
theorem numeric488 (p : Pattern) (guard : d126873 p = 1) (decreasing : d17560 p < d0 p) :
    d48251 p + d0 p ≤ (0 : Int) + d48388 p + d17560 p := by
  have beforeRange := bonus_range 138 p
  rw [at138] at beforeRange
  have afterRange := bonus_range 160 (HazardPattern.afterPattern 10000 p (.walk 160))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) ∧ bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) ≤ 2 at afterRange
  rw [gammaAfter488] at afterRange
  have possibilities : (d0 p = 1 ∧ d17560 p = 0) ∨ (d0 p = 2 ∧ d17560 p = 0) ∨ (d0 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro23120 p beforeEq guard
    have complete := andIntro23121 p combined afterEq
    have bound := compare10073 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro23120 p beforeEq guard
    have complete := andIntro23121 p combined afterEq
    have bound := compare10074 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro23120 p beforeEq guard
    have complete := andIntro23122 p combined afterEq
    have bound := compare10073 p complete
    omega
theorem local488 (p : Pattern) (guard : d126873 p = 1)
    (decreasing : bonus 160 (HazardPattern.afterPattern 10000 p (.walk 160)) < bonus 138 p) :
    NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 138 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 160) + NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 160))) + bonus 160 (HazardPattern.afterPattern 10000 p (.walk 160)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 160) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) < bonus 138 p at decreasing
  rw [gammaAfter488, at138] at decreasing
  have numeric := numeric488 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160))
  rw [oldBefore138, at138, literal, oldAfter488, gammaAfter488]
  exact numeric
theorem numeric489 (p : Pattern) (guard : d128487 p = 1) (decreasing : d0 p < d0 p) :
    d48251 p + d0 p ≤ (0 : Int) + d128576 p + d0 p := by
  have beforeRange := bonus_range 138 p
  rw [at138] at beforeRange
  have afterRange := bonus_range 160 (HazardPattern.afterPattern 10000 p (.push 160 (.stay 182)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 160 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 182))) ∧ bonus (HazardPattern.nextHero (.push 160 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 182))) ≤ 2 at afterRange
  rw [gammaAfter489] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro23123 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10075 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro23123 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10076 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro23123 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10075 p complete
    omega
theorem local489 (p : Pattern) (guard : d128487 p = 1)
    (decreasing : bonus 160 (HazardPattern.afterPattern 10000 p (.push 160 (.stay 182))) < bonus 138 p) :
    NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 138 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 160 (.stay 182)) + NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 160 (.stay 182)))) + bonus 160 (HazardPattern.afterPattern 10000 p (.push 160 (.stay 182))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 160 (.stay 182)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 160 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 182))) < bonus 138 p at decreasing
  rw [gammaAfter489, at138] at decreasing
  have numeric := numeric489 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 160 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 182)))
  rw [oldBefore138, at138, literal, oldAfter489, gammaAfter489]
  exact numeric
end NetHack.Soko22Hazard87
