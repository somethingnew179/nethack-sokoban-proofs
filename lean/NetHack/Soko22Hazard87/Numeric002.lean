import NetHack.Soko22Hazard87.Numeric001
import NetHack.Soko22Hazard87.AndIntroBlocks0036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric140 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 78 p
  rw [at78] at beforeRange
  have afterRange := bonus_range 79 (HazardPattern.afterPattern 10000 p (.walk 79))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) ∧ bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) ≤ 2 at afterRange
  rw [gammaAfter140] at afterRange
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
theorem local140 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 79 (HazardPattern.afterPattern 10000 p (.walk 79)) < bonus 78 p) :
    NetHack.Sokoban22Refined85.bonus 78 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 78 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 79) + NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 79))) + bonus 79 (HazardPattern.afterPattern 10000 p (.walk 79)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 79) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) < bonus 78 p at decreasing
  rw [gammaAfter140, at78] at decreasing
  have numeric := numeric140 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79))
  rw [oldBefore78, at78, literal, oldAfter140, gammaAfter140]
  exact numeric
theorem numeric141 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 78 p
  rw [at78] at beforeRange
  have afterRange := bonus_range 79 (HazardPattern.afterPattern 10000 p (.push 79 (.stay 80)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 79 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 79 (.stay 80))) ∧ bonus (HazardPattern.nextHero (.push 79 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 79 (.stay 80))) ≤ 2 at afterRange
  rw [gammaAfter141] at afterRange
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
theorem local141 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 79 (HazardPattern.afterPattern 10000 p (.push 79 (.stay 80))) < bonus 78 p) :
    NetHack.Sokoban22Refined85.bonus 78 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 78 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 79 (.stay 80)) + NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 79 (.stay 80)))) + bonus 79 (HazardPattern.afterPattern 10000 p (.push 79 (.stay 80))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 79 (.stay 80)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 79 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 79 (.stay 80))) < bonus 78 p at decreasing
  rw [gammaAfter141, at78] at decreasing
  have numeric := numeric141 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 79 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 79 (.stay 80)))
  rw [oldBefore78, at78, literal, oldAfter141, gammaAfter141]
  exact numeric
theorem numeric142 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 78 p
  rw [at78] at beforeRange
  have afterRange := bonus_range 101 (HazardPattern.afterPattern 10000 p (.walk 101))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ∧ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ≤ 2 at afterRange
  rw [gammaAfter142] at afterRange
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
theorem local142 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 78 p) :
    NetHack.Sokoban22Refined85.bonus 78 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 78 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 101) + NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 101))) + bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 101) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 78 p at decreasing
  rw [gammaAfter142, at78] at decreasing
  have numeric := numeric142 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101))
  rw [oldBefore78, at78, literal, oldAfter142, gammaAfter142]
  exact numeric
theorem numeric143 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 79 p
  rw [at79] at beforeRange
  have afterRange := bonus_range 101 (HazardPattern.afterPattern 10000 p (.walk 101))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ∧ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ≤ 2 at afterRange
  rw [gammaAfter143] at afterRange
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
theorem local143 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 79 p) :
    NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 79 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 101) + NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 101))) + bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 101) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 79 p at decreasing
  rw [gammaAfter143, at79] at decreasing
  have numeric := numeric143 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101))
  rw [oldBefore79, at79, literal, oldAfter143, gammaAfter143]
  exact numeric
theorem numeric144 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 79 p
  rw [at79] at beforeRange
  have afterRange := bonus_range 101 (HazardPattern.afterPattern 10000 p (.push 101 (.stay 123)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 101 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 123))) ∧ bonus (HazardPattern.nextHero (.push 101 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 123))) ≤ 2 at afterRange
  rw [gammaAfter144] at afterRange
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
theorem local144 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 101 (HazardPattern.afterPattern 10000 p (.push 101 (.stay 123))) < bonus 79 p) :
    NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 79 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 101 (.stay 123)) + NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 101 (.stay 123)))) + bonus 101 (HazardPattern.afterPattern 10000 p (.push 101 (.stay 123))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 101 (.stay 123)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 101 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 123))) < bonus 79 p at decreasing
  rw [gammaAfter144, at79] at decreasing
  have numeric := numeric144 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 101 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 123)))
  rw [oldBefore79, at79, literal, oldAfter144, gammaAfter144]
  exact numeric
theorem numeric145 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 79 p
  rw [at79] at beforeRange
  have afterRange := bonus_range 80 (HazardPattern.afterPattern 10000 p (.walk 80))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) ∧ bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) ≤ 2 at afterRange
  rw [gammaAfter145] at afterRange
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
theorem local145 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 80 (HazardPattern.afterPattern 10000 p (.walk 80)) < bonus 79 p) :
    NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 79 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 80) + NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 80))) + bonus 80 (HazardPattern.afterPattern 10000 p (.walk 80)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 80) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) < bonus 79 p at decreasing
  rw [gammaAfter145, at79] at decreasing
  have numeric := numeric145 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80))
  rw [oldBefore79, at79, literal, oldAfter145, gammaAfter145]
  exact numeric
theorem numeric146 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 79 p
  rw [at79] at beforeRange
  have afterRange := bonus_range 80 (HazardPattern.afterPattern 10000 p (.push 80 (.stay 81)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 80 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 80 (.stay 81))) ∧ bonus (HazardPattern.nextHero (.push 80 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 80 (.stay 81))) ≤ 2 at afterRange
  rw [gammaAfter146] at afterRange
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
theorem local146 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 80 (HazardPattern.afterPattern 10000 p (.push 80 (.stay 81))) < bonus 79 p) :
    NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 79 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 80 (.stay 81)) + NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 80 (.stay 81)))) + bonus 80 (HazardPattern.afterPattern 10000 p (.push 80 (.stay 81))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 80 (.stay 81)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 80 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 80 (.stay 81))) < bonus 79 p at decreasing
  rw [gammaAfter146, at79] at decreasing
  have numeric := numeric146 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 80 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 80 (.stay 81)))
  rw [oldBefore79, at79, literal, oldAfter146, gammaAfter146]
  exact numeric
theorem numeric147 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 79 p
  rw [at79] at beforeRange
  have afterRange := bonus_range 78 (HazardPattern.afterPattern 10000 p (.walk 78))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78)) ∧ bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78)) ≤ 2 at afterRange
  rw [gammaAfter147] at afterRange
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
theorem local147 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 78 (HazardPattern.afterPattern 10000 p (.walk 78)) < bonus 79 p) :
    NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 79 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 78) + NetHack.Sokoban22Refined85.bonus 78 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 78))) + bonus 78 (HazardPattern.afterPattern 10000 p (.walk 78)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 78) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78)) < bonus 79 p at decreasing
  rw [gammaAfter147, at79] at decreasing
  have numeric := numeric147 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78))
  rw [oldBefore79, at79, literal, oldAfter147, gammaAfter147]
  exact numeric
theorem numeric148 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 79 p
  rw [at79] at beforeRange
  have afterRange := bonus_range 102 (HazardPattern.afterPattern 10000 p (.walk 102))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ∧ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ≤ 2 at afterRange
  rw [gammaAfter148] at afterRange
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
theorem local148 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 79 p) :
    NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 79 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 102) + NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 102))) + bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 102) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 79 p at decreasing
  rw [gammaAfter148, at79] at decreasing
  have numeric := numeric148 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102))
  rw [oldBefore79, at79, literal, oldAfter148, gammaAfter148]
  exact numeric
theorem numeric149 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 79 p
  rw [at79] at beforeRange
  have afterRange := bonus_range 100 (HazardPattern.afterPattern 10000 p (.walk 100))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) ∧ bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) ≤ 2 at afterRange
  rw [gammaAfter149] at afterRange
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
theorem local149 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 100 (HazardPattern.afterPattern 10000 p (.walk 100)) < bonus 79 p) :
    NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 79 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 100) + NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 100))) + bonus 100 (HazardPattern.afterPattern 10000 p (.walk 100)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 100) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) < bonus 79 p at decreasing
  rw [gammaAfter149, at79] at decreasing
  have numeric := numeric149 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100))
  rw [oldBefore79, at79, literal, oldAfter149, gammaAfter149]
  exact numeric
theorem numeric150 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 80 p
  rw [at80] at beforeRange
  have afterRange := bonus_range 102 (HazardPattern.afterPattern 10000 p (.walk 102))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ∧ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ≤ 2 at afterRange
  rw [gammaAfter150] at afterRange
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
theorem local150 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 80 p) :
    NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 80 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 102) + NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 102))) + bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 102) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 80 p at decreasing
  rw [gammaAfter150, at80] at decreasing
  have numeric := numeric150 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102))
  rw [oldBefore80, at80, literal, oldAfter150, gammaAfter150]
  exact numeric
theorem numeric151 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 80 p
  rw [at80] at beforeRange
  have afterRange := bonus_range 102 (HazardPattern.afterPattern 10000 p (.push 102 (.stay 124)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 102 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 124))) ∧ bonus (HazardPattern.nextHero (.push 102 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 124))) ≤ 2 at afterRange
  rw [gammaAfter151] at afterRange
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
theorem local151 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 102 (HazardPattern.afterPattern 10000 p (.push 102 (.stay 124))) < bonus 80 p) :
    NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 80 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 102 (.stay 124)) + NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 102 (.stay 124)))) + bonus 102 (HazardPattern.afterPattern 10000 p (.push 102 (.stay 124))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 102 (.stay 124)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 102 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 124))) < bonus 80 p at decreasing
  rw [gammaAfter151, at80] at decreasing
  have numeric := numeric151 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 102 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 124)))
  rw [oldBefore80, at80, literal, oldAfter151, gammaAfter151]
  exact numeric
theorem numeric152 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 80 p
  rw [at80] at beforeRange
  have afterRange := bonus_range 81 (HazardPattern.afterPattern 10000 p (.walk 81))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) ∧ bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) ≤ 2 at afterRange
  rw [gammaAfter152] at afterRange
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
theorem local152 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 81 (HazardPattern.afterPattern 10000 p (.walk 81)) < bonus 80 p) :
    NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 80 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 81) + NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 81))) + bonus 81 (HazardPattern.afterPattern 10000 p (.walk 81)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 81) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) < bonus 80 p at decreasing
  rw [gammaAfter152, at80] at decreasing
  have numeric := numeric152 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81))
  rw [oldBefore80, at80, literal, oldAfter152, gammaAfter152]
  exact numeric
theorem numeric153 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 80 p
  rw [at80] at beforeRange
  have afterRange := bonus_range 81 (HazardPattern.afterPattern 10000 p (.push 81 (.stay 82)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 81 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 81 (.stay 82))) ∧ bonus (HazardPattern.nextHero (.push 81 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 81 (.stay 82))) ≤ 2 at afterRange
  rw [gammaAfter153] at afterRange
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
theorem local153 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 81 (HazardPattern.afterPattern 10000 p (.push 81 (.stay 82))) < bonus 80 p) :
    NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 80 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 81 (.stay 82)) + NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 81 (.stay 82)))) + bonus 81 (HazardPattern.afterPattern 10000 p (.push 81 (.stay 82))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 81 (.stay 82)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 81 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 81 (.stay 82))) < bonus 80 p at decreasing
  rw [gammaAfter153, at80] at decreasing
  have numeric := numeric153 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 81 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 81 (.stay 82)))
  rw [oldBefore80, at80, literal, oldAfter153, gammaAfter153]
  exact numeric
theorem numeric154 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 80 p
  rw [at80] at beforeRange
  have afterRange := bonus_range 79 (HazardPattern.afterPattern 10000 p (.walk 79))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) ∧ bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) ≤ 2 at afterRange
  rw [gammaAfter154] at afterRange
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
theorem local154 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 79 (HazardPattern.afterPattern 10000 p (.walk 79)) < bonus 80 p) :
    NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 80 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 79) + NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 79))) + bonus 79 (HazardPattern.afterPattern 10000 p (.walk 79)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 79) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) < bonus 80 p at decreasing
  rw [gammaAfter154, at80] at decreasing
  have numeric := numeric154 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79))
  rw [oldBefore80, at80, literal, oldAfter154, gammaAfter154]
  exact numeric
theorem numeric155 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 80 p
  rw [at80] at beforeRange
  have afterRange := bonus_range 79 (HazardPattern.afterPattern 10000 p (.push 79 (.stay 78)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 79 (.stay 78))) (HazardPattern.afterPattern 10000 p (.push 79 (.stay 78))) ∧ bonus (HazardPattern.nextHero (.push 79 (.stay 78))) (HazardPattern.afterPattern 10000 p (.push 79 (.stay 78))) ≤ 2 at afterRange
  rw [gammaAfter155] at afterRange
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
theorem local155 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 79 (HazardPattern.afterPattern 10000 p (.push 79 (.stay 78))) < bonus 80 p) :
    NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 80 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 79 (.stay 78)) + NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 79 (.stay 78)))) + bonus 79 (HazardPattern.afterPattern 10000 p (.push 79 (.stay 78))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 79 (.stay 78)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 79 (.stay 78))) (HazardPattern.afterPattern 10000 p (.push 79 (.stay 78))) < bonus 80 p at decreasing
  rw [gammaAfter155, at80] at decreasing
  have numeric := numeric155 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 79 (.stay 78))) (HazardPattern.afterPattern 10000 p (.push 79 (.stay 78)))
  rw [oldBefore80, at80, literal, oldAfter155, gammaAfter155]
  exact numeric
theorem numeric156 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 80 p
  rw [at80] at beforeRange
  have afterRange := bonus_range 103 (HazardPattern.afterPattern 10000 p (.walk 103))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ∧ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ≤ 2 at afterRange
  rw [gammaAfter156] at afterRange
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
theorem local156 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 80 p) :
    NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 80 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 103) + NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 103))) + bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 103) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 80 p at decreasing
  rw [gammaAfter156, at80] at decreasing
  have numeric := numeric156 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103))
  rw [oldBefore80, at80, literal, oldAfter156, gammaAfter156]
  exact numeric
theorem numeric157 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 80 p
  rw [at80] at beforeRange
  have afterRange := bonus_range 101 (HazardPattern.afterPattern 10000 p (.walk 101))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ∧ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ≤ 2 at afterRange
  rw [gammaAfter157] at afterRange
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
theorem local157 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 80 p) :
    NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 80 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 101) + NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 101))) + bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 101) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 80 p at decreasing
  rw [gammaAfter157, at80] at decreasing
  have numeric := numeric157 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101))
  rw [oldBefore80, at80, literal, oldAfter157, gammaAfter157]
  exact numeric
theorem numeric158 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 81 p
  rw [at81] at beforeRange
  have afterRange := bonus_range 103 (HazardPattern.afterPattern 10000 p (.walk 103))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ∧ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ≤ 2 at afterRange
  rw [gammaAfter158] at afterRange
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
theorem local158 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 81 p) :
    NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 81 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 103) + NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 103))) + bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 103) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 81 p at decreasing
  rw [gammaAfter158, at81] at decreasing
  have numeric := numeric158 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103))
  rw [oldBefore81, at81, literal, oldAfter158, gammaAfter158]
  exact numeric
theorem numeric159 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 81 p
  rw [at81] at beforeRange
  have afterRange := bonus_range 103 (HazardPattern.afterPattern 10000 p (.push 103 (.stay 125)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 103 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 125))) ∧ bonus (HazardPattern.nextHero (.push 103 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 125))) ≤ 2 at afterRange
  rw [gammaAfter159] at afterRange
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
theorem local159 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 103 (HazardPattern.afterPattern 10000 p (.push 103 (.stay 125))) < bonus 81 p) :
    NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 81 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 103 (.stay 125)) + NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 103 (.stay 125)))) + bonus 103 (HazardPattern.afterPattern 10000 p (.push 103 (.stay 125))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 103 (.stay 125)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 103 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 125))) < bonus 81 p at decreasing
  rw [gammaAfter159, at81] at decreasing
  have numeric := numeric159 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 103 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 125)))
  rw [oldBefore81, at81, literal, oldAfter159, gammaAfter159]
  exact numeric
theorem numeric160 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 81 p
  rw [at81] at beforeRange
  have afterRange := bonus_range 82 (HazardPattern.afterPattern 10000 p (.walk 82))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) ∧ bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) ≤ 2 at afterRange
  rw [gammaAfter160] at afterRange
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
theorem local160 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 82 (HazardPattern.afterPattern 10000 p (.walk 82)) < bonus 81 p) :
    NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 81 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 82) + NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 82))) + bonus 82 (HazardPattern.afterPattern 10000 p (.walk 82)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 82) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) < bonus 81 p at decreasing
  rw [gammaAfter160, at81] at decreasing
  have numeric := numeric160 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82))
  rw [oldBefore81, at81, literal, oldAfter160, gammaAfter160]
  exact numeric
theorem numeric161 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 81 p
  rw [at81] at beforeRange
  have afterRange := bonus_range 82 (HazardPattern.afterPattern 10000 p (.push 82 (.stay 83)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 82 (.stay 83))) (HazardPattern.afterPattern 10000 p (.push 82 (.stay 83))) ∧ bonus (HazardPattern.nextHero (.push 82 (.stay 83))) (HazardPattern.afterPattern 10000 p (.push 82 (.stay 83))) ≤ 2 at afterRange
  rw [gammaAfter161] at afterRange
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
theorem local161 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 82 (HazardPattern.afterPattern 10000 p (.push 82 (.stay 83))) < bonus 81 p) :
    NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 81 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 82 (.stay 83)) + NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 82 (.stay 83)))) + bonus 82 (HazardPattern.afterPattern 10000 p (.push 82 (.stay 83))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 82 (.stay 83)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 82 (.stay 83))) (HazardPattern.afterPattern 10000 p (.push 82 (.stay 83))) < bonus 81 p at decreasing
  rw [gammaAfter161, at81] at decreasing
  have numeric := numeric161 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 82 (.stay 83))) (HazardPattern.afterPattern 10000 p (.push 82 (.stay 83)))
  rw [oldBefore81, at81, literal, oldAfter161, gammaAfter161]
  exact numeric
theorem numeric162 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 81 p
  rw [at81] at beforeRange
  have afterRange := bonus_range 80 (HazardPattern.afterPattern 10000 p (.walk 80))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) ∧ bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) ≤ 2 at afterRange
  rw [gammaAfter162] at afterRange
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
theorem local162 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 80 (HazardPattern.afterPattern 10000 p (.walk 80)) < bonus 81 p) :
    NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 81 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 80) + NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 80))) + bonus 80 (HazardPattern.afterPattern 10000 p (.walk 80)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 80) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) < bonus 81 p at decreasing
  rw [gammaAfter162, at81] at decreasing
  have numeric := numeric162 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80))
  rw [oldBefore81, at81, literal, oldAfter162, gammaAfter162]
  exact numeric
theorem numeric163 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 81 p
  rw [at81] at beforeRange
  have afterRange := bonus_range 80 (HazardPattern.afterPattern 10000 p (.push 80 (.stay 79)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 80 (.stay 79))) (HazardPattern.afterPattern 10000 p (.push 80 (.stay 79))) ∧ bonus (HazardPattern.nextHero (.push 80 (.stay 79))) (HazardPattern.afterPattern 10000 p (.push 80 (.stay 79))) ≤ 2 at afterRange
  rw [gammaAfter163] at afterRange
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
theorem local163 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 80 (HazardPattern.afterPattern 10000 p (.push 80 (.stay 79))) < bonus 81 p) :
    NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 81 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 80 (.stay 79)) + NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 80 (.stay 79)))) + bonus 80 (HazardPattern.afterPattern 10000 p (.push 80 (.stay 79))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 80 (.stay 79)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 80 (.stay 79))) (HazardPattern.afterPattern 10000 p (.push 80 (.stay 79))) < bonus 81 p at decreasing
  rw [gammaAfter163, at81] at decreasing
  have numeric := numeric163 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 80 (.stay 79))) (HazardPattern.afterPattern 10000 p (.push 80 (.stay 79)))
  rw [oldBefore81, at81, literal, oldAfter163, gammaAfter163]
  exact numeric
theorem numeric164 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 81 p
  rw [at81] at beforeRange
  have afterRange := bonus_range 104 (HazardPattern.afterPattern 10000 p (.walk 104))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ∧ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ≤ 2 at afterRange
  rw [gammaAfter164] at afterRange
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
theorem local164 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 81 p) :
    NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 81 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 104) + NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 104))) + bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 104) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 81 p at decreasing
  rw [gammaAfter164, at81] at decreasing
  have numeric := numeric164 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104))
  rw [oldBefore81, at81, literal, oldAfter164, gammaAfter164]
  exact numeric
theorem numeric165 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 81 p
  rw [at81] at beforeRange
  have afterRange := bonus_range 102 (HazardPattern.afterPattern 10000 p (.walk 102))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ∧ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ≤ 2 at afterRange
  rw [gammaAfter165] at afterRange
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
theorem local165 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 81 p) :
    NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 81 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 102) + NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 102))) + bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 102) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 81 p at decreasing
  rw [gammaAfter165, at81] at decreasing
  have numeric := numeric165 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102))
  rw [oldBefore81, at81, literal, oldAfter165, gammaAfter165]
  exact numeric
theorem numeric166 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 82 p
  rw [at82] at beforeRange
  have afterRange := bonus_range 104 (HazardPattern.afterPattern 10000 p (.walk 104))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ∧ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ≤ 2 at afterRange
  rw [gammaAfter166] at afterRange
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
theorem local166 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 82 p) :
    NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 82 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 104) + NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 104))) + bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 104) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 82 p at decreasing
  rw [gammaAfter166, at82] at decreasing
  have numeric := numeric166 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104))
  rw [oldBefore82, at82, literal, oldAfter166, gammaAfter166]
  exact numeric
theorem numeric167 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 82 p
  rw [at82] at beforeRange
  have afterRange := bonus_range 104 (HazardPattern.afterPattern 10000 p (.push 104 (.stay 126)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 104 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 126))) ∧ bonus (HazardPattern.nextHero (.push 104 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 126))) ≤ 2 at afterRange
  rw [gammaAfter167] at afterRange
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
theorem local167 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 104 (HazardPattern.afterPattern 10000 p (.push 104 (.stay 126))) < bonus 82 p) :
    NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 82 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 104 (.stay 126)) + NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 104 (.stay 126)))) + bonus 104 (HazardPattern.afterPattern 10000 p (.push 104 (.stay 126))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 104 (.stay 126)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 104 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 126))) < bonus 82 p at decreasing
  rw [gammaAfter167, at82] at decreasing
  have numeric := numeric167 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 104 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 126)))
  rw [oldBefore82, at82, literal, oldAfter167, gammaAfter167]
  exact numeric
theorem numeric168 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 82 p
  rw [at82] at beforeRange
  have afterRange := bonus_range 83 (HazardPattern.afterPattern 10000 p (.walk 83))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) ∧ bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) ≤ 2 at afterRange
  rw [gammaAfter168] at afterRange
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
theorem local168 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 83 (HazardPattern.afterPattern 10000 p (.walk 83)) < bonus 82 p) :
    NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 82 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 83) + NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 83))) + bonus 83 (HazardPattern.afterPattern 10000 p (.walk 83)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 83) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) < bonus 82 p at decreasing
  rw [gammaAfter168, at82] at decreasing
  have numeric := numeric168 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83))
  rw [oldBefore82, at82, literal, oldAfter168, gammaAfter168]
  exact numeric
theorem numeric169 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 82 p
  rw [at82] at beforeRange
  have afterRange := bonus_range 83 (HazardPattern.afterPattern 10000 p (.push 83 (.stay 84)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 83 (.stay 84))) (HazardPattern.afterPattern 10000 p (.push 83 (.stay 84))) ∧ bonus (HazardPattern.nextHero (.push 83 (.stay 84))) (HazardPattern.afterPattern 10000 p (.push 83 (.stay 84))) ≤ 2 at afterRange
  rw [gammaAfter169] at afterRange
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
theorem local169 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 83 (HazardPattern.afterPattern 10000 p (.push 83 (.stay 84))) < bonus 82 p) :
    NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 82 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 83 (.stay 84)) + NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 83 (.stay 84)))) + bonus 83 (HazardPattern.afterPattern 10000 p (.push 83 (.stay 84))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 83 (.stay 84)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 83 (.stay 84))) (HazardPattern.afterPattern 10000 p (.push 83 (.stay 84))) < bonus 82 p at decreasing
  rw [gammaAfter169, at82] at decreasing
  have numeric := numeric169 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 83 (.stay 84))) (HazardPattern.afterPattern 10000 p (.push 83 (.stay 84)))
  rw [oldBefore82, at82, literal, oldAfter169, gammaAfter169]
  exact numeric
theorem numeric170 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 82 p
  rw [at82] at beforeRange
  have afterRange := bonus_range 81 (HazardPattern.afterPattern 10000 p (.walk 81))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) ∧ bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) ≤ 2 at afterRange
  rw [gammaAfter170] at afterRange
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
theorem local170 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 81 (HazardPattern.afterPattern 10000 p (.walk 81)) < bonus 82 p) :
    NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 82 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 81) + NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 81))) + bonus 81 (HazardPattern.afterPattern 10000 p (.walk 81)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 81) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) < bonus 82 p at decreasing
  rw [gammaAfter170, at82] at decreasing
  have numeric := numeric170 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81))
  rw [oldBefore82, at82, literal, oldAfter170, gammaAfter170]
  exact numeric
theorem numeric171 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 82 p
  rw [at82] at beforeRange
  have afterRange := bonus_range 81 (HazardPattern.afterPattern 10000 p (.push 81 (.stay 80)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 81 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 81 (.stay 80))) ∧ bonus (HazardPattern.nextHero (.push 81 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 81 (.stay 80))) ≤ 2 at afterRange
  rw [gammaAfter171] at afterRange
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
theorem local171 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 81 (HazardPattern.afterPattern 10000 p (.push 81 (.stay 80))) < bonus 82 p) :
    NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 82 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 81 (.stay 80)) + NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 81 (.stay 80)))) + bonus 81 (HazardPattern.afterPattern 10000 p (.push 81 (.stay 80))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 81 (.stay 80)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 81 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 81 (.stay 80))) < bonus 82 p at decreasing
  rw [gammaAfter171, at82] at decreasing
  have numeric := numeric171 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 81 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 81 (.stay 80)))
  rw [oldBefore82, at82, literal, oldAfter171, gammaAfter171]
  exact numeric
theorem numeric172 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 82 p
  rw [at82] at beforeRange
  have afterRange := bonus_range 105 (HazardPattern.afterPattern 10000 p (.walk 105))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ∧ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ≤ 2 at afterRange
  rw [gammaAfter172] at afterRange
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
theorem local172 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 82 p) :
    NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 82 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 105) + NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 105))) + bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 105) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 82 p at decreasing
  rw [gammaAfter172, at82] at decreasing
  have numeric := numeric172 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105))
  rw [oldBefore82, at82, literal, oldAfter172, gammaAfter172]
  exact numeric
theorem numeric173 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 82 p
  rw [at82] at beforeRange
  have afterRange := bonus_range 103 (HazardPattern.afterPattern 10000 p (.walk 103))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ∧ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ≤ 2 at afterRange
  rw [gammaAfter173] at afterRange
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
theorem local173 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 82 p) :
    NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 82 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 103) + NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 103))) + bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 103) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 82 p at decreasing
  rw [gammaAfter173, at82] at decreasing
  have numeric := numeric173 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103))
  rw [oldBefore82, at82, literal, oldAfter173, gammaAfter173]
  exact numeric
theorem numeric174 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 83 p
  rw [at83] at beforeRange
  have afterRange := bonus_range 105 (HazardPattern.afterPattern 10000 p (.walk 105))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ∧ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ≤ 2 at afterRange
  rw [gammaAfter174] at afterRange
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
theorem local174 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 83 p) :
    NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 83 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 105) + NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 105))) + bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 105) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 83 p at decreasing
  rw [gammaAfter174, at83] at decreasing
  have numeric := numeric174 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105))
  rw [oldBefore83, at83, literal, oldAfter174, gammaAfter174]
  exact numeric
theorem numeric175 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 83 p
  rw [at83] at beforeRange
  have afterRange := bonus_range 105 (HazardPattern.afterPattern 10000 p (.push 105 (.stay 127)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 105 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 127))) ∧ bonus (HazardPattern.nextHero (.push 105 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 127))) ≤ 2 at afterRange
  rw [gammaAfter175] at afterRange
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
theorem local175 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 105 (HazardPattern.afterPattern 10000 p (.push 105 (.stay 127))) < bonus 83 p) :
    NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 83 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 105 (.stay 127)) + NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 105 (.stay 127)))) + bonus 105 (HazardPattern.afterPattern 10000 p (.push 105 (.stay 127))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 105 (.stay 127)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 105 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 127))) < bonus 83 p at decreasing
  rw [gammaAfter175, at83] at decreasing
  have numeric := numeric175 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 105 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 127)))
  rw [oldBefore83, at83, literal, oldAfter175, gammaAfter175]
  exact numeric
theorem numeric176 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 83 p
  rw [at83] at beforeRange
  have afterRange := bonus_range 84 (HazardPattern.afterPattern 10000 p (.walk 84))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84)) ∧ bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84)) ≤ 2 at afterRange
  rw [gammaAfter176] at afterRange
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
theorem local176 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 84 (HazardPattern.afterPattern 10000 p (.walk 84)) < bonus 83 p) :
    NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 83 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 84) + NetHack.Sokoban22Refined85.bonus 84 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 84))) + bonus 84 (HazardPattern.afterPattern 10000 p (.walk 84)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 84) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84)) < bonus 83 p at decreasing
  rw [gammaAfter176, at83] at decreasing
  have numeric := numeric176 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84))
  rw [oldBefore83, at83, literal, oldAfter176, gammaAfter176]
  exact numeric
theorem numeric177 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 83 p
  rw [at83] at beforeRange
  have afterRange := bonus_range 82 (HazardPattern.afterPattern 10000 p (.walk 82))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) ∧ bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) ≤ 2 at afterRange
  rw [gammaAfter177] at afterRange
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
theorem local177 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 82 (HazardPattern.afterPattern 10000 p (.walk 82)) < bonus 83 p) :
    NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 83 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 82) + NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 82))) + bonus 82 (HazardPattern.afterPattern 10000 p (.walk 82)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 82) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) < bonus 83 p at decreasing
  rw [gammaAfter177, at83] at decreasing
  have numeric := numeric177 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82))
  rw [oldBefore83, at83, literal, oldAfter177, gammaAfter177]
  exact numeric
theorem numeric178 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 83 p
  rw [at83] at beforeRange
  have afterRange := bonus_range 82 (HazardPattern.afterPattern 10000 p (.push 82 (.stay 81)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 82 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 82 (.stay 81))) ∧ bonus (HazardPattern.nextHero (.push 82 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 82 (.stay 81))) ≤ 2 at afterRange
  rw [gammaAfter178] at afterRange
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
theorem local178 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 82 (HazardPattern.afterPattern 10000 p (.push 82 (.stay 81))) < bonus 83 p) :
    NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 83 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 82 (.stay 81)) + NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 82 (.stay 81)))) + bonus 82 (HazardPattern.afterPattern 10000 p (.push 82 (.stay 81))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 82 (.stay 81)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 82 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 82 (.stay 81))) < bonus 83 p at decreasing
  rw [gammaAfter178, at83] at decreasing
  have numeric := numeric178 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 82 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 82 (.stay 81)))
  rw [oldBefore83, at83, literal, oldAfter178, gammaAfter178]
  exact numeric
theorem numeric179 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 83 p
  rw [at83] at beforeRange
  have afterRange := bonus_range 106 (HazardPattern.afterPattern 10000 p (.walk 106))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) ∧ bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) ≤ 2 at afterRange
  rw [gammaAfter179] at afterRange
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
theorem local179 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 106 (HazardPattern.afterPattern 10000 p (.walk 106)) < bonus 83 p) :
    NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 83 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 106) + NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 106))) + bonus 106 (HazardPattern.afterPattern 10000 p (.walk 106)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 106) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) < bonus 83 p at decreasing
  rw [gammaAfter179, at83] at decreasing
  have numeric := numeric179 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106))
  rw [oldBefore83, at83, literal, oldAfter179, gammaAfter179]
  exact numeric
theorem numeric180 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 83 p
  rw [at83] at beforeRange
  have afterRange := bonus_range 104 (HazardPattern.afterPattern 10000 p (.walk 104))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ∧ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ≤ 2 at afterRange
  rw [gammaAfter180] at afterRange
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
theorem local180 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 83 p) :
    NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 83 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 104) + NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 104))) + bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 104) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 83 p at decreasing
  rw [gammaAfter180, at83] at decreasing
  have numeric := numeric180 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104))
  rw [oldBefore83, at83, literal, oldAfter180, gammaAfter180]
  exact numeric
theorem numeric181 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 84 p
  rw [at84] at beforeRange
  have afterRange := bonus_range 106 (HazardPattern.afterPattern 10000 p (.walk 106))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) ∧ bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) ≤ 2 at afterRange
  rw [gammaAfter181] at afterRange
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
theorem local181 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 106 (HazardPattern.afterPattern 10000 p (.walk 106)) < bonus 84 p) :
    NetHack.Sokoban22Refined85.bonus 84 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 84 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 106) + NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 106))) + bonus 106 (HazardPattern.afterPattern 10000 p (.walk 106)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 106) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) < bonus 84 p at decreasing
  rw [gammaAfter181, at84] at decreasing
  have numeric := numeric181 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106))
  rw [oldBefore84, at84, literal, oldAfter181, gammaAfter181]
  exact numeric
theorem numeric182 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 84 p
  rw [at84] at beforeRange
  have afterRange := bonus_range 106 (HazardPattern.afterPattern 10000 p (.push 106 (.stay 128)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 106 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 106 (.stay 128))) ∧ bonus (HazardPattern.nextHero (.push 106 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 106 (.stay 128))) ≤ 2 at afterRange
  rw [gammaAfter182] at afterRange
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
theorem local182 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 106 (HazardPattern.afterPattern 10000 p (.push 106 (.stay 128))) < bonus 84 p) :
    NetHack.Sokoban22Refined85.bonus 84 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 84 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 106 (.stay 128)) + NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 106 (.stay 128)))) + bonus 106 (HazardPattern.afterPattern 10000 p (.push 106 (.stay 128))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 106 (.stay 128)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 106 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 106 (.stay 128))) < bonus 84 p at decreasing
  rw [gammaAfter182, at84] at decreasing
  have numeric := numeric182 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 106 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 106 (.stay 128)))
  rw [oldBefore84, at84, literal, oldAfter182, gammaAfter182]
  exact numeric
theorem numeric183 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 84 p
  rw [at84] at beforeRange
  have afterRange := bonus_range 83 (HazardPattern.afterPattern 10000 p (.walk 83))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) ∧ bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) ≤ 2 at afterRange
  rw [gammaAfter183] at afterRange
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
theorem local183 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 83 (HazardPattern.afterPattern 10000 p (.walk 83)) < bonus 84 p) :
    NetHack.Sokoban22Refined85.bonus 84 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 84 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 83) + NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 83))) + bonus 83 (HazardPattern.afterPattern 10000 p (.walk 83)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 83) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) < bonus 84 p at decreasing
  rw [gammaAfter183, at84] at decreasing
  have numeric := numeric183 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83))
  rw [oldBefore84, at84, literal, oldAfter183, gammaAfter183]
  exact numeric
theorem numeric184 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 84 p
  rw [at84] at beforeRange
  have afterRange := bonus_range 83 (HazardPattern.afterPattern 10000 p (.push 83 (.stay 82)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 83 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 83 (.stay 82))) ∧ bonus (HazardPattern.nextHero (.push 83 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 83 (.stay 82))) ≤ 2 at afterRange
  rw [gammaAfter184] at afterRange
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
theorem local184 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 83 (HazardPattern.afterPattern 10000 p (.push 83 (.stay 82))) < bonus 84 p) :
    NetHack.Sokoban22Refined85.bonus 84 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 84 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 83 (.stay 82)) + NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 83 (.stay 82)))) + bonus 83 (HazardPattern.afterPattern 10000 p (.push 83 (.stay 82))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 83 (.stay 82)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 83 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 83 (.stay 82))) < bonus 84 p at decreasing
  rw [gammaAfter184, at84] at decreasing
  have numeric := numeric184 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 83 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 83 (.stay 82)))
  rw [oldBefore84, at84, literal, oldAfter184, gammaAfter184]
  exact numeric
theorem numeric185 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 84 p
  rw [at84] at beforeRange
  have afterRange := bonus_range 105 (HazardPattern.afterPattern 10000 p (.walk 105))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ∧ bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) ≤ 2 at afterRange
  rw [gammaAfter185] at afterRange
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
theorem local185 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 84 p) :
    NetHack.Sokoban22Refined85.bonus 84 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 84 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 105) + NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 105))) + bonus 105 (HazardPattern.afterPattern 10000 p (.walk 105)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 105) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) < bonus 84 p at decreasing
  rw [gammaAfter185, at84] at decreasing
  have numeric := numeric185 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105))
  rw [oldBefore84, at84, literal, oldAfter185, gammaAfter185]
  exact numeric
theorem numeric186 (p : Pattern) (guard : d67301 p = 1) (decreasing : d2518 p < d4334 p) :
    d47866 p + d4334 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 89 p
  rw [at89] at beforeRange
  have afterRange := bonus_range 67 (HazardPattern.afterPattern 10000 p (.walk 67))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67)) ∧ bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67)) ≤ 2 at afterRange
  rw [gammaAfter186] at afterRange
  have possibilities : (d4334 p = 1 ∧ d2518 p = 0) ∨ (d4334 p = 2 ∧ d2518 p = 0) ∨ (d4334 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2682 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro6783 p guard beforeEq
    have complete := andIntro6832 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3336 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro3779 p beforeEq guard
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3336 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro3779 p beforeEq guard
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local186 (p : Pattern) (guard : d67301 p = 1)
    (decreasing : bonus 67 (HazardPattern.afterPattern 10000 p (.walk 67)) < bonus 89 p) :
    NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 89 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 67) + NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 67))) + bonus 67 (HazardPattern.afterPattern 10000 p (.walk 67)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 67) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67)) < bonus 89 p at decreasing
  rw [gammaAfter186, at89] at decreasing
  have numeric := numeric186 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67))
  rw [oldBefore89, at89, literal, oldAfter186, gammaAfter186]
  exact numeric
theorem numeric187 (p : Pattern) (guard : d57576 p = 1) (decreasing : d0 p < d4334 p) :
    d47866 p + d4334 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 89 p
  rw [at89] at beforeRange
  have afterRange := bonus_range 67 (HazardPattern.afterPattern 10000 p (.push 67 (.stay 45)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 67 (.stay 45))) (HazardPattern.afterPattern 10000 p (.push 67 (.stay 45))) ∧ bonus (HazardPattern.nextHero (.push 67 (.stay 45))) (HazardPattern.afterPattern 10000 p (.push 67 (.stay 45))) ≤ 2 at afterRange
  rw [gammaAfter187] at afterRange
  have possibilities : (d4334 p = 1 ∧ d0 p = 0) ∨ (d4334 p = 2 ∧ d0 p = 0) ∨ (d4334 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2682 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6834 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro3336 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro1098 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3336 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro1098 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2 p complete
    omega
theorem local187 (p : Pattern) (guard : d57576 p = 1)
    (decreasing : bonus 67 (HazardPattern.afterPattern 10000 p (.push 67 (.stay 45))) < bonus 89 p) :
    NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 89 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 67 (.stay 45)) + NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 67 (.stay 45)))) + bonus 67 (HazardPattern.afterPattern 10000 p (.push 67 (.stay 45))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 67 (.stay 45)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 67 (.stay 45))) (HazardPattern.afterPattern 10000 p (.push 67 (.stay 45))) < bonus 89 p at decreasing
  rw [gammaAfter187, at89] at decreasing
  have numeric := numeric187 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 67 (.stay 45))) (HazardPattern.afterPattern 10000 p (.push 67 (.stay 45)))
  rw [oldBefore89, at89, literal, oldAfter187, gammaAfter187]
  exact numeric
theorem numeric188 (p : Pattern) (guard : d74075 p = 1) (decreasing : d5849 p < d4334 p) :
    d47866 p + d4334 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 89 p
  rw [at89] at beforeRange
  have afterRange := bonus_range 111 (HazardPattern.afterPattern 10000 p (.walk 111))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) ∧ bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) ≤ 2 at afterRange
  rw [gammaAfter188] at afterRange
  have possibilities : (d4334 p = 1 ∧ d5849 p = 0) ∨ (d4334 p = 2 ∧ d5849 p = 0) ∨ (d4334 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2682 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro6835 p beforeEq guard
    have complete := andIntro6879 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3336 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro6880 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3336 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro6880 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local188 (p : Pattern) (guard : d74075 p = 1)
    (decreasing : bonus 111 (HazardPattern.afterPattern 10000 p (.walk 111)) < bonus 89 p) :
    NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 89 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 111) + NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 111))) + bonus 111 (HazardPattern.afterPattern 10000 p (.walk 111)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 111) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) < bonus 89 p at decreasing
  rw [gammaAfter188, at89] at decreasing
  have numeric := numeric188 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111))
  rw [oldBefore89, at89, literal, oldAfter188, gammaAfter188]
  exact numeric
theorem numeric189 (p : Pattern) (guard : d74854 p = 1) (decreasing : d0 p < d4334 p) :
    d47866 p + d4334 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 89 p
  rw [at89] at beforeRange
  have afterRange := bonus_range 111 (HazardPattern.afterPattern 10000 p (.push 111 (.stay 133)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 111 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 111 (.stay 133))) ∧ bonus (HazardPattern.nextHero (.push 111 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 111 (.stay 133))) ≤ 2 at afterRange
  rw [gammaAfter189] at afterRange
  have possibilities : (d4334 p = 1 ∧ d0 p = 0) ∨ (d4334 p = 2 ∧ d0 p = 0) ∨ (d4334 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2682 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6971 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro3336 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6974 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3336 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6974 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2 p complete
    omega
theorem local189 (p : Pattern) (guard : d74854 p = 1)
    (decreasing : bonus 111 (HazardPattern.afterPattern 10000 p (.push 111 (.stay 133))) < bonus 89 p) :
    NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 89 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 111 (.stay 133)) + NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 111 (.stay 133)))) + bonus 111 (HazardPattern.afterPattern 10000 p (.push 111 (.stay 133))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 111 (.stay 133)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 111 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 111 (.stay 133))) < bonus 89 p at decreasing
  rw [gammaAfter189, at89] at decreasing
  have numeric := numeric189 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 111 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 111 (.stay 133)))
  rw [oldBefore89, at89, literal, oldAfter189, gammaAfter189]
  exact numeric
theorem numeric190 (p : Pattern) (guard : d68222 p = 1) (decreasing : d4650 p < d4334 p) :
    d47866 p + d4334 p ≤ (0 : Int) + d47866 p + d4650 p := by
  have beforeRange := bonus_range 89 p
  rw [at89] at beforeRange
  have afterRange := bonus_range 90 (HazardPattern.afterPattern 10000 p (.walk 90))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) ∧ bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) ≤ 2 at afterRange
  rw [gammaAfter190] at afterRange
  have possibilities : (d4334 p = 1 ∧ d4650 p = 0) ∨ (d4334 p = 2 ∧ d4650 p = 0) ∨ (d4334 p = 2 ∧ d4650 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2682 p pair.1
    have afterEq := eqIntro2731 p pair.2
    have combined := andIntro7009 p beforeEq guard
    have complete := andIntro4139 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3336 p pair.1
    have afterEq := eqIntro2731 p pair.2
    have combined := andIntro7011 p beforeEq guard
    have complete := andIntro4173 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3336 p pair.1
    have afterEq := eqIntro2732 p pair.2
    have combined := andIntro7011 p beforeEq guard
    have complete := andIntro4174 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local190 (p : Pattern) (guard : d68222 p = 1)
    (decreasing : bonus 90 (HazardPattern.afterPattern 10000 p (.walk 90)) < bonus 89 p) :
    NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 89 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 90) + NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 90))) + bonus 90 (HazardPattern.afterPattern 10000 p (.walk 90)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 90) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) < bonus 89 p at decreasing
  rw [gammaAfter190, at89] at decreasing
  have numeric := numeric190 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90))
  rw [oldBefore89, at89, literal, oldAfter190, gammaAfter190]
  exact numeric
theorem numeric191 (p : Pattern) (guard : d74857 p = 1) (decreasing : d75152 p < d4334 p) :
    d47866 p + d4334 p ≤ (1 : Int) + d47866 p + d75152 p := by
  have beforeRange := bonus_range 89 p
  rw [at89] at beforeRange
  have afterRange := bonus_range 90 (HazardPattern.afterPattern 10000 p (.push 90 (.stay 91)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 90 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 90 (.stay 91))) ∧ bonus (HazardPattern.nextHero (.push 90 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 90 (.stay 91))) ≤ 2 at afterRange
  rw [gammaAfter191] at afterRange
  have possibilities : (d4334 p = 1 ∧ d75152 p = 0) ∨ (d4334 p = 2 ∧ d75152 p = 0) ∨ (d4334 p = 2 ∧ d75152 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2682 p pair.1
    have afterEq := eqIntro3518 p pair.2
    have combined := andIntro7083 p beforeEq guard
    have complete := andIntro7084 p afterEq combined
    have bound := compare4376 p complete
    omega
  · have beforeEq := eqIntro3336 p pair.1
    have afterEq := eqIntro3518 p pair.2
    have combined := andIntro7116 p beforeEq guard
    have complete := andIntro7165 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3336 p pair.1
    have afterEq := eqIntro3519 p pair.2
    have combined := andIntro7116 p beforeEq guard
    have complete := andIntro7166 p combined afterEq
    have bound := compare4377 p complete
    omega
theorem local191 (p : Pattern) (guard : d74857 p = 1)
    (decreasing : bonus 90 (HazardPattern.afterPattern 10000 p (.push 90 (.stay 91))) < bonus 89 p) :
    NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 89 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 90 (.stay 91)) + NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 90 (.stay 91)))) + bonus 90 (HazardPattern.afterPattern 10000 p (.push 90 (.stay 91))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 90 (.stay 91)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 90 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 90 (.stay 91))) < bonus 89 p at decreasing
  rw [gammaAfter191, at89] at decreasing
  have numeric := numeric191 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 90 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 90 (.stay 91)))
  rw [oldBefore89, at89, literal, oldAfter191, gammaAfter191]
  exact numeric
theorem numeric192 (p : Pattern) (guard : d73190 p = 1) (decreasing : d5349 p < d4650 p) :
    d47866 p + d4650 p ≤ (0 : Int) + d47866 p + d5349 p := by
  have beforeRange := bonus_range 90 p
  rw [at90] at beforeRange
  have afterRange := bonus_range 91 (HazardPattern.afterPattern 10000 p (.walk 91))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) ∧ bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) ≤ 2 at afterRange
  rw [gammaAfter192] at afterRange
  have possibilities : (d4650 p = 1 ∧ d5349 p = 0) ∨ (d4650 p = 2 ∧ d5349 p = 0) ∨ (d4650 p = 2 ∧ d5349 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2732 p pair.1
    have afterEq := eqIntro2844 p pair.2
    have combined := andIntro7201 p beforeEq guard
    have complete := andIntro7236 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3568 p pair.1
    have afterEq := eqIntro2844 p pair.2
    have combined := andIntro7237 p beforeEq guard
    have complete := andIntro7238 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3568 p pair.1
    have afterEq := eqIntro2893 p pair.2
    have combined := andIntro7237 p beforeEq guard
    have complete := andIntro7239 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local192 (p : Pattern) (guard : d73190 p = 1)
    (decreasing : bonus 91 (HazardPattern.afterPattern 10000 p (.walk 91)) < bonus 90 p) :
    NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 90 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 91) + NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 91))) + bonus 91 (HazardPattern.afterPattern 10000 p (.walk 91)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 91) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) < bonus 90 p at decreasing
  rw [gammaAfter192, at90] at decreasing
  have numeric := numeric192 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91))
  rw [oldBefore90, at90, literal, oldAfter192, gammaAfter192]
  exact numeric
theorem numeric193 (p : Pattern) (guard : d68222 p = 1) (decreasing : d4334 p < d4650 p) :
    d47866 p + d4650 p ≤ (0 : Int) + d47866 p + d4334 p := by
  have beforeRange := bonus_range 90 p
  rw [at90] at beforeRange
  have afterRange := bonus_range 89 (HazardPattern.afterPattern 10000 p (.walk 89))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89)) ∧ bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89)) ≤ 2 at afterRange
  rw [gammaAfter193] at afterRange
  have possibilities : (d4650 p = 1 ∧ d4334 p = 0) ∨ (d4650 p = 2 ∧ d4334 p = 0) ∨ (d4650 p = 2 ∧ d4334 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2732 p pair.1
    have afterEq := eqIntro2633 p pair.2
    have combined := andIntro7274 p beforeEq guard
    have complete := andIntro7309 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3568 p pair.1
    have afterEq := eqIntro2633 p pair.2
    have combined := andIntro7310 p beforeEq guard
    have complete := andIntro7311 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3568 p pair.1
    have afterEq := eqIntro2682 p pair.2
    have combined := andIntro7310 p beforeEq guard
    have complete := andIntro7312 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local193 (p : Pattern) (guard : d68222 p = 1)
    (decreasing : bonus 89 (HazardPattern.afterPattern 10000 p (.walk 89)) < bonus 90 p) :
    NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 90 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 89) + NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 89))) + bonus 89 (HazardPattern.afterPattern 10000 p (.walk 89)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 89) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89)) < bonus 90 p at decreasing
  rw [gammaAfter193, at90] at decreasing
  have numeric := numeric193 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89))
  rw [oldBefore90, at90, literal, oldAfter193, gammaAfter193]
  exact numeric
theorem numeric194 (p : Pattern) (guard : d73191 p = 1) (decreasing : d3318 p < d4650 p) :
    d47866 p + d4650 p ≤ (0 : Int) + d47866 p + d3318 p := by
  have beforeRange := bonus_range 90 p
  rw [at90] at beforeRange
  have afterRange := bonus_range 69 (HazardPattern.afterPattern 10000 p (.walk 69))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) ∧ bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) ≤ 2 at afterRange
  rw [gammaAfter194] at afterRange
  have possibilities : (d4650 p = 1 ∧ d3318 p = 0) ∨ (d4650 p = 2 ∧ d3318 p = 0) ∨ (d4650 p = 2 ∧ d3318 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2732 p pair.1
    have afterEq := eqIntro1766 p pair.2
    have combined := andIntro7333 p beforeEq guard
    have complete := andIntro7382 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3568 p pair.1
    have afterEq := eqIntro1766 p pair.2
    have combined := andIntro7383 p beforeEq guard
    have complete := andIntro7384 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3568 p pair.1
    have afterEq := eqIntro1787 p pair.2
    have combined := andIntro7383 p beforeEq guard
    have complete := andIntro7385 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local194 (p : Pattern) (guard : d73191 p = 1)
    (decreasing : bonus 69 (HazardPattern.afterPattern 10000 p (.walk 69)) < bonus 90 p) :
    NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 90 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 69) + NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 69))) + bonus 69 (HazardPattern.afterPattern 10000 p (.walk 69)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 69) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) < bonus 90 p at decreasing
  rw [gammaAfter194, at90] at decreasing
  have numeric := numeric194 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69))
  rw [oldBefore90, at90, literal, oldAfter194, gammaAfter194]
  exact numeric
theorem numeric195 (p : Pattern) (guard : d68223 p = 1) (decreasing : d2518 p < d4650 p) :
    d47866 p + d4650 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 90 p
  rw [at90] at beforeRange
  have afterRange := bonus_range 67 (HazardPattern.afterPattern 10000 p (.walk 67))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67)) ∧ bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67)) ≤ 2 at afterRange
  rw [gammaAfter195] at afterRange
  have possibilities : (d4650 p = 1 ∧ d2518 p = 0) ∨ (d4650 p = 2 ∧ d2518 p = 0) ∨ (d4650 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2732 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro7387 p beforeEq guard
    have complete := andIntro7422 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3568 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro7423 p beforeEq guard
    have complete := andIntro7424 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3568 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro7423 p beforeEq guard
    have complete := andIntro7425 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local195 (p : Pattern) (guard : d68223 p = 1)
    (decreasing : bonus 67 (HazardPattern.afterPattern 10000 p (.walk 67)) < bonus 90 p) :
    NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 90 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 67) + NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 67))) + bonus 67 (HazardPattern.afterPattern 10000 p (.walk 67)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 67) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67)) < bonus 90 p at decreasing
  rw [gammaAfter195, at90] at decreasing
  have numeric := numeric195 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67))
  rw [oldBefore90, at90, literal, oldAfter195, gammaAfter195]
  exact numeric
theorem numeric196 (p : Pattern) (guard : d75630 p = 1) (decreasing : d6737 p < d4650 p) :
    d47866 p + d4650 p ≤ (0 : Int) + d47866 p + d6737 p := by
  have beforeRange := bonus_range 90 p
  rw [at90] at beforeRange
  have afterRange := bonus_range 113 (HazardPattern.afterPattern 10000 p (.walk 113))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) ∧ bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) ≤ 2 at afterRange
  rw [gammaAfter196] at afterRange
  have possibilities : (d4650 p = 1 ∧ d6737 p = 0) ∨ (d4650 p = 2 ∧ d6737 p = 0) ∨ (d4650 p = 2 ∧ d6737 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2732 p pair.1
    have afterEq := eqIntro3730 p pair.2
    have combined := andIntro7492 p beforeEq guard
    have complete := andIntro7577 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3568 p pair.1
    have afterEq := eqIntro3730 p pair.2
    have combined := andIntro7578 p beforeEq guard
    have complete := andIntro7579 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3568 p pair.1
    have afterEq := eqIntro3797 p pair.2
    have combined := andIntro7578 p beforeEq guard
    have complete := andIntro7580 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local196 (p : Pattern) (guard : d75630 p = 1)
    (decreasing : bonus 113 (HazardPattern.afterPattern 10000 p (.walk 113)) < bonus 90 p) :
    NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 90 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 113) + NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 113))) + bonus 113 (HazardPattern.afterPattern 10000 p (.walk 113)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 113) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) < bonus 90 p at decreasing
  rw [gammaAfter196, at90] at decreasing
  have numeric := numeric196 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113))
  rw [oldBefore90, at90, literal, oldAfter196, gammaAfter196]
  exact numeric
theorem numeric197 (p : Pattern) (guard : d77113 p = 1) (decreasing : d5849 p < d4650 p) :
    d47866 p + d4650 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 90 p
  rw [at90] at beforeRange
  have afterRange := bonus_range 111 (HazardPattern.afterPattern 10000 p (.walk 111))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) ∧ bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) ≤ 2 at afterRange
  rw [gammaAfter197] at afterRange
  have possibilities : (d4650 p = 1 ∧ d5849 p = 0) ∨ (d4650 p = 2 ∧ d5849 p = 0) ∨ (d4650 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2732 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro7583 p beforeEq guard
    have complete := andIntro7615 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3568 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro7616 p beforeEq guard
    have complete := andIntro7617 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3568 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro7616 p beforeEq guard
    have complete := andIntro7618 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local197 (p : Pattern) (guard : d77113 p = 1)
    (decreasing : bonus 111 (HazardPattern.afterPattern 10000 p (.walk 111)) < bonus 90 p) :
    NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 90 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 111) + NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 111))) + bonus 111 (HazardPattern.afterPattern 10000 p (.walk 111)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 111) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) < bonus 90 p at decreasing
  rw [gammaAfter197, at90] at decreasing
  have numeric := numeric197 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111))
  rw [oldBefore90, at90, literal, oldAfter197, gammaAfter197]
  exact numeric
theorem numeric198 (p : Pattern) (guard : d68751 p = 1) (decreasing : d3318 p < d5349 p) :
    d47866 p + d5349 p ≤ (0 : Int) + d47866 p + d3318 p := by
  have beforeRange := bonus_range 91 p
  rw [at91] at beforeRange
  have afterRange := bonus_range 69 (HazardPattern.afterPattern 10000 p (.walk 69))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) ∧ bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) ≤ 2 at afterRange
  rw [gammaAfter198] at afterRange
  have possibilities : (d5349 p = 1 ∧ d3318 p = 0) ∨ (d5349 p = 2 ∧ d3318 p = 0) ∨ (d5349 p = 2 ∧ d3318 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2893 p pair.1
    have afterEq := eqIntro1766 p pair.2
    have combined := andIntro7639 p guard beforeEq
    have complete := andIntro7686 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro1766 p pair.2
    have combined := andIntro7687 p guard beforeEq
    have complete := andIntro7731 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro1787 p pair.2
    have combined := andIntro7687 p guard beforeEq
    have complete := andIntro7775 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local198 (p : Pattern) (guard : d68751 p = 1)
    (decreasing : bonus 69 (HazardPattern.afterPattern 10000 p (.walk 69)) < bonus 91 p) :
    NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 91 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 69) + NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 69))) + bonus 69 (HazardPattern.afterPattern 10000 p (.walk 69)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 69) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) < bonus 91 p at decreasing
  rw [gammaAfter198, at91] at decreasing
  have numeric := numeric198 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69))
  rw [oldBefore91, at91, literal, oldAfter198, gammaAfter198]
  exact numeric
theorem numeric199 (p : Pattern) (guard : d58750 p = 1) (decreasing : d0 p < d5349 p) :
    d47866 p + d5349 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 91 p
  rw [at91] at beforeRange
  have afterRange := bonus_range 69 (HazardPattern.afterPattern 10000 p (.push 69 (.stay 47)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 69 (.stay 47))) (HazardPattern.afterPattern 10000 p (.push 69 (.stay 47))) ∧ bonus (HazardPattern.nextHero (.push 69 (.stay 47))) (HazardPattern.afterPattern 10000 p (.push 69 (.stay 47))) ≤ 2 at afterRange
  rw [gammaAfter199] at afterRange
  have possibilities : (d5349 p = 1 ∧ d0 p = 0) ∨ (d5349 p = 2 ∧ d0 p = 0) ∨ (d5349 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2893 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro7796 p guard beforeEq
    have complete := andIntro7797 p afterEq combined
    have bound := compare4378 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro7817 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro7817 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2 p complete
    omega
theorem local199 (p : Pattern) (guard : d58750 p = 1)
    (decreasing : bonus 69 (HazardPattern.afterPattern 10000 p (.push 69 (.stay 47))) < bonus 91 p) :
    NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 91 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 69 (.stay 47)) + NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 69 (.stay 47)))) + bonus 69 (HazardPattern.afterPattern 10000 p (.push 69 (.stay 47))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 69 (.stay 47)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 69 (.stay 47))) (HazardPattern.afterPattern 10000 p (.push 69 (.stay 47))) < bonus 91 p at decreasing
  rw [gammaAfter199, at91] at decreasing
  have numeric := numeric199 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 69 (.stay 47))) (HazardPattern.afterPattern 10000 p (.push 69 (.stay 47)))
  rw [oldBefore91, at91, literal, oldAfter199, gammaAfter199]
  exact numeric
theorem numeric200 (p : Pattern) (guard : d75629 p = 1) (decreasing : d6737 p < d5349 p) :
    d47866 p + d5349 p ≤ (0 : Int) + d47866 p + d6737 p := by
  have beforeRange := bonus_range 91 p
  rw [at91] at beforeRange
  have afterRange := bonus_range 113 (HazardPattern.afterPattern 10000 p (.walk 113))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) ∧ bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) ≤ 2 at afterRange
  rw [gammaAfter200] at afterRange
  have possibilities : (d5349 p = 1 ∧ d6737 p = 0) ∨ (d5349 p = 2 ∧ d6737 p = 0) ∨ (d5349 p = 2 ∧ d6737 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2893 p pair.1
    have afterEq := eqIntro3730 p pair.2
    have combined := andIntro7902 p beforeEq guard
    have complete := andIntro8002 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro3730 p pair.2
    have combined := andIntro8034 p beforeEq guard
    have complete := andIntro8083 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro3797 p pair.2
    have combined := andIntro8034 p beforeEq guard
    have complete := andIntro8132 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local200 (p : Pattern) (guard : d75629 p = 1)
    (decreasing : bonus 113 (HazardPattern.afterPattern 10000 p (.walk 113)) < bonus 91 p) :
    NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 91 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 113) + NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 113))) + bonus 113 (HazardPattern.afterPattern 10000 p (.walk 113)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 113) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) < bonus 91 p at decreasing
  rw [gammaAfter200, at91] at decreasing
  have numeric := numeric200 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113))
  rw [oldBefore91, at91, literal, oldAfter200, gammaAfter200]
  exact numeric
theorem numeric201 (p : Pattern) (guard : d77845 p = 1) (decreasing : d78794 p < d5349 p) :
    d47866 p + d5349 p ≤ (0 : Int) + d47866 p + d78794 p := by
  have beforeRange := bonus_range 91 p
  rw [at91] at beforeRange
  have afterRange := bonus_range 113 (HazardPattern.afterPattern 10000 p (.push 113 (.stay 135)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 113 (.stay 135))) (HazardPattern.afterPattern 10000 p (.push 113 (.stay 135))) ∧ bonus (HazardPattern.nextHero (.push 113 (.stay 135))) (HazardPattern.afterPattern 10000 p (.push 113 (.stay 135))) ≤ 2 at afterRange
  rw [gammaAfter201] at afterRange
  have possibilities : (d5349 p = 1 ∧ d78794 p = 0) ∨ (d5349 p = 2 ∧ d78794 p = 0) ∨ (d5349 p = 2 ∧ d78794 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2893 p pair.1
    have afterEq := eqIntro4094 p pair.2
    have combined := andIntro8324 p beforeEq guard
    have complete := andIntro8469 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro4094 p pair.2
    have combined := andIntro8502 p beforeEq guard
    have complete := andIntro8546 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro4168 p pair.2
    have combined := andIntro8502 p beforeEq guard
    have complete := andIntro8590 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local201 (p : Pattern) (guard : d77845 p = 1)
    (decreasing : bonus 113 (HazardPattern.afterPattern 10000 p (.push 113 (.stay 135))) < bonus 91 p) :
    NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 91 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 113 (.stay 135)) + NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 113 (.stay 135)))) + bonus 113 (HazardPattern.afterPattern 10000 p (.push 113 (.stay 135))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 113 (.stay 135)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 113 (.stay 135))) (HazardPattern.afterPattern 10000 p (.push 113 (.stay 135))) < bonus 91 p at decreasing
  rw [gammaAfter201, at91] at decreasing
  have numeric := numeric201 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 113 (.stay 135))) (HazardPattern.afterPattern 10000 p (.push 113 (.stay 135)))
  rw [oldBefore91, at91, literal, oldAfter201, gammaAfter201]
  exact numeric
theorem numeric202 (p : Pattern) (guard : d73190 p = 1) (decreasing : d4650 p < d5349 p) :
    d47866 p + d5349 p ≤ (0 : Int) + d47866 p + d4650 p := by
  have beforeRange := bonus_range 91 p
  rw [at91] at beforeRange
  have afterRange := bonus_range 90 (HazardPattern.afterPattern 10000 p (.walk 90))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) ∧ bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) ≤ 2 at afterRange
  rw [gammaAfter202] at afterRange
  have possibilities : (d5349 p = 1 ∧ d4650 p = 0) ∨ (d5349 p = 2 ∧ d4650 p = 0) ∨ (d5349 p = 2 ∧ d4650 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2893 p pair.1
    have afterEq := eqIntro2731 p pair.2
    have combined := andIntro8659 p beforeEq guard
    have complete := andIntro5180 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro2731 p pair.2
    have combined := andIntro8692 p beforeEq guard
    have complete := andIntro4173 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro2732 p pair.2
    have combined := andIntro8692 p beforeEq guard
    have complete := andIntro4174 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local202 (p : Pattern) (guard : d73190 p = 1)
    (decreasing : bonus 90 (HazardPattern.afterPattern 10000 p (.walk 90)) < bonus 91 p) :
    NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 91 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 90) + NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 90))) + bonus 90 (HazardPattern.afterPattern 10000 p (.walk 90)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 90) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) < bonus 91 p at decreasing
  rw [gammaAfter202, at91] at decreasing
  have numeric := numeric202 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90))
  rw [oldBefore91, at91, literal, oldAfter202, gammaAfter202]
  exact numeric
theorem numeric203 (p : Pattern) (guard : d74857 p = 1) (decreasing : d81124 p < d5349 p) :
    d47866 p + d5349 p ≤ (1 : Int) + d47866 p + d81124 p := by
  have beforeRange := bonus_range 91 p
  rw [at91] at beforeRange
  have afterRange := bonus_range 90 (HazardPattern.afterPattern 10000 p (.push 90 (.stay 89)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 90 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 90 (.stay 89))) ∧ bonus (HazardPattern.nextHero (.push 90 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 90 (.stay 89))) ≤ 2 at afterRange
  rw [gammaAfter203] at afterRange
  have possibilities : (d5349 p = 1 ∧ d81124 p = 0) ∨ (d5349 p = 2 ∧ d81124 p = 0) ∨ (d5349 p = 2 ∧ d81124 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2893 p pair.1
    have afterEq := eqIntro4217 p pair.2
    have combined := andIntro8741 p beforeEq guard
    have complete := andIntro8742 p afterEq combined
    have bound := compare4379 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro4217 p pair.2
    have combined := andIntro8743 p beforeEq guard
    have complete := andIntro8792 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro4218 p pair.2
    have combined := andIntro8743 p beforeEq guard
    have complete := andIntro8793 p combined afterEq
    have bound := compare4377 p complete
    omega
theorem local203 (p : Pattern) (guard : d74857 p = 1)
    (decreasing : bonus 90 (HazardPattern.afterPattern 10000 p (.push 90 (.stay 89))) < bonus 91 p) :
    NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 91 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 90 (.stay 89)) + NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 90 (.stay 89)))) + bonus 90 (HazardPattern.afterPattern 10000 p (.push 90 (.stay 89))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 90 (.stay 89)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 90 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 90 (.stay 89))) < bonus 91 p at decreasing
  rw [gammaAfter203, at91] at decreasing
  have numeric := numeric203 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 90 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 90 (.stay 89)))
  rw [oldBefore91, at91, literal, oldAfter203, gammaAfter203]
  exact numeric
theorem numeric204 (p : Pattern) (guard : d73495 p = 1) (decreasing : d3496 p < d5349 p) :
    d47866 p + d5349 p ≤ (0 : Int) + d47866 p + d3496 p := by
  have beforeRange := bonus_range 91 p
  rw [at91] at beforeRange
  have afterRange := bonus_range 70 (HazardPattern.afterPattern 10000 p (.walk 70))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ∧ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ≤ 2 at afterRange
  rw [gammaAfter204] at afterRange
  have possibilities : (d5349 p = 1 ∧ d3496 p = 0) ∨ (d5349 p = 2 ∧ d3496 p = 0) ∨ (d5349 p = 2 ∧ d3496 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2893 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro8815 p beforeEq guard
    have complete := andIntro8836 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro8857 p beforeEq guard
    have complete := andIntro8877 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro1978 p pair.2
    have combined := andIntro8857 p beforeEq guard
    have complete := andIntro8897 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local204 (p : Pattern) (guard : d73495 p = 1)
    (decreasing : bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 91 p) :
    NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 91 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 70) + NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 70))) + bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 70) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 91 p at decreasing
  rw [gammaAfter204, at91] at decreasing
  have numeric := numeric204 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70))
  rw [oldBefore91, at91, literal, oldAfter204, gammaAfter204]
  exact numeric
theorem numeric205 (p : Pattern) (guard : d81525 p = 1) (decreasing : d7239 p < d5349 p) :
    d47866 p + d5349 p ≤ (0 : Int) + d47866 p + d7239 p := by
  have beforeRange := bonus_range 91 p
  rw [at91] at beforeRange
  have afterRange := bonus_range 114 (HazardPattern.afterPattern 10000 p (.walk 114))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) ∧ bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) ≤ 2 at afterRange
  rw [gammaAfter205] at afterRange
  have possibilities : (d5349 p = 1 ∧ d7239 p = 0) ∨ (d5349 p = 2 ∧ d7239 p = 0) ∨ (d5349 p = 2 ∧ d7239 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2893 p pair.1
    have afterEq := eqIntro4312 p pair.2
    have combined := andIntro8900 p beforeEq guard
    have complete := andIntro9027 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro4312 p pair.2
    have combined := andIntro9030 p beforeEq guard
    have complete := andIntro9079 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3888 p pair.1
    have afterEq := eqIntro4356 p pair.2
    have combined := andIntro9030 p beforeEq guard
    have complete := andIntro9123 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local205 (p : Pattern) (guard : d81525 p = 1)
    (decreasing : bonus 114 (HazardPattern.afterPattern 10000 p (.walk 114)) < bonus 91 p) :
    NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 91 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 114) + NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 114))) + bonus 114 (HazardPattern.afterPattern 10000 p (.walk 114)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 114) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) < bonus 91 p at decreasing
  rw [gammaAfter205, at91] at decreasing
  have numeric := numeric205 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114))
  rw [oldBefore91, at91, literal, oldAfter205, gammaAfter205]
  exact numeric
theorem numeric206 (p : Pattern) (guard : d73492 p = 1) (decreasing : d3673 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d48087 p + d3673 p := by
  have beforeRange := bonus_range 93 p
  rw [at93] at beforeRange
  have afterRange := bonus_range 71 (HazardPattern.afterPattern 10000 p (.walk 71))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) ∧ bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) ≤ 2 at afterRange
  rw [gammaAfter206] at afterRange
  have possibilities : (d0 p = 1 ∧ d3673 p = 0) ∨ (d0 p = 2 ∧ d3673 p = 0) ∨ (d0 p = 2 ∧ d3673 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro2078 p pair.2
    have combined := andIntro9124 p beforeEq guard
    have complete := andIntro2923 p combined afterEq
    have bound := compare2476 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2078 p pair.2
    have combined := andIntro9124 p beforeEq guard
    have complete := andIntro2923 p combined afterEq
    have bound := compare2477 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2106 p pair.2
    have combined := andIntro9124 p beforeEq guard
    have complete := andIntro2924 p combined afterEq
    have bound := compare2476 p complete
    omega
theorem local206 (p : Pattern) (guard : d73492 p = 1)
    (decreasing : bonus 71 (HazardPattern.afterPattern 10000 p (.walk 71)) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 71) + NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 71))) + bonus 71 (HazardPattern.afterPattern 10000 p (.walk 71)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 71) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) < bonus 93 p at decreasing
  rw [gammaAfter206, at93] at decreasing
  have numeric := numeric206 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71))
  rw [oldBefore93, at93, literal, oldAfter206, gammaAfter206]
  exact numeric
theorem numeric207 (p : Pattern) (guard : d62939 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (2 : Int) + d47700 p + d0 p := by
  have beforeRange := bonus_range 93 p
  rw [at93] at beforeRange
  have afterRange := bonus_range 71 (HazardPattern.afterPattern 10000 p (.push 71 (.stay 49)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 71 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 71 (.stay 49))) ∧ bonus (HazardPattern.nextHero (.push 71 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 71 (.stay 49))) ≤ 2 at afterRange
  rw [gammaAfter207] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9125 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4380 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9125 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare2317 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9125 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4380 p complete
    omega
theorem local207 (p : Pattern) (guard : d62939 p = 1)
    (decreasing : bonus 71 (HazardPattern.afterPattern 10000 p (.push 71 (.stay 49))) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 71 (.stay 49)) + NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 71 (.stay 49)))) + bonus 71 (HazardPattern.afterPattern 10000 p (.push 71 (.stay 49))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 71 (.stay 49)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 71 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 71 (.stay 49))) < bonus 93 p at decreasing
  rw [gammaAfter207, at93] at decreasing
  have numeric := numeric207 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 71 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 71 (.stay 49)))
  rw [oldBefore93, at93, literal, oldAfter207, gammaAfter207]
  exact numeric
theorem numeric208 (p : Pattern) (guard : d82320 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d48097 p + d0 p := by
  have beforeRange := bonus_range 93 p
  rw [at93] at beforeRange
  have afterRange := bonus_range 115 (HazardPattern.afterPattern 10000 p (.walk 115))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) ∧ bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) ≤ 2 at afterRange
  rw [gammaAfter208] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9126 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4381 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9126 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4382 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9126 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4381 p complete
    omega
theorem local208 (p : Pattern) (guard : d82320 p = 1)
    (decreasing : bonus 115 (HazardPattern.afterPattern 10000 p (.walk 115)) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 115) + NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 115))) + bonus 115 (HazardPattern.afterPattern 10000 p (.walk 115)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 115) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) < bonus 93 p at decreasing
  rw [gammaAfter208, at93] at decreasing
  have numeric := numeric208 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115))
  rw [oldBefore93, at93, literal, oldAfter208, gammaAfter208]
  exact numeric
theorem numeric209 (p : Pattern) (guard : d82321 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 93 p
  rw [at93] at beforeRange
  have afterRange := bonus_range 94 (HazardPattern.afterPattern 10000 p (.walk 94))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) ∧ bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) ≤ 2 at afterRange
  rw [gammaAfter209] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9127 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9127 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9127 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local209 (p : Pattern) (guard : d82321 p = 1)
    (decreasing : bonus 94 (HazardPattern.afterPattern 10000 p (.walk 94)) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 94) + NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 94))) + bonus 94 (HazardPattern.afterPattern 10000 p (.walk 94)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 94) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) < bonus 93 p at decreasing
  rw [gammaAfter209, at93] at decreasing
  have numeric := numeric209 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94))
  rw [oldBefore93, at93, literal, oldAfter209, gammaAfter209]
  exact numeric
end NetHack.Soko22Hazard87
