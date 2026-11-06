import NetHack.Soko22Hazard87.Numeric009
import NetHack.Soko22Hazard87.AndIntroBlocks0223
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric700 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 170 p
  rw [at170] at beforeRange
  have afterRange := bonus_range 171 (HazardPattern.afterPattern 10000 p (.walk 171))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ∧ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ≤ 2 at afterRange
  rw [gammaAfter700] at afterRange
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
theorem local700 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 171) + NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 171))) + bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 171) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 170 p at decreasing
  rw [gammaAfter700, at170] at decreasing
  have numeric := numeric700 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171))
  rw [oldBefore170, at170, literal, oldAfter700, gammaAfter700]
  exact numeric
theorem numeric701 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 170 p
  rw [at170] at beforeRange
  have afterRange := bonus_range 171 (HazardPattern.afterPattern 10000 p (.push 171 (.stay 172)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 171 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 172))) ∧ bonus (HazardPattern.nextHero (.push 171 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 172))) ≤ 2 at afterRange
  rw [gammaAfter701] at afterRange
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
theorem local701 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 171 (HazardPattern.afterPattern 10000 p (.push 171 (.stay 172))) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 171 (.stay 172)) + NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 171 (.stay 172)))) + bonus 171 (HazardPattern.afterPattern 10000 p (.push 171 (.stay 172))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 171 (.stay 172)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 171 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 172))) < bonus 170 p at decreasing
  rw [gammaAfter701, at170] at decreasing
  have numeric := numeric701 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 171 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 172)))
  rw [oldBefore170, at170, literal, oldAfter701, gammaAfter701]
  exact numeric
theorem numeric702 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 170 p
  rw [at170] at beforeRange
  have afterRange := bonus_range 169 (HazardPattern.afterPattern 10000 p (.walk 169))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ∧ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ≤ 2 at afterRange
  rw [gammaAfter702] at afterRange
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
theorem local702 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 169) + NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) + bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 169) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 170 p at decreasing
  rw [gammaAfter702, at170] at decreasing
  have numeric := numeric702 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169))
  rw [oldBefore170, at170, literal, oldAfter702, gammaAfter702]
  exact numeric
theorem numeric703 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 170 p
  rw [at170] at beforeRange
  have afterRange := bonus_range 169 (HazardPattern.afterPattern 10000 p (.push 169 (.stay 168)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 169 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 168))) ∧ bonus (HazardPattern.nextHero (.push 169 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 168))) ≤ 2 at afterRange
  rw [gammaAfter703] at afterRange
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
theorem local703 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 169 (HazardPattern.afterPattern 10000 p (.push 169 (.stay 168))) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 169 (.stay 168)) + NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 169 (.stay 168)))) + bonus 169 (HazardPattern.afterPattern 10000 p (.push 169 (.stay 168))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 169 (.stay 168)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 169 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 168))) < bonus 170 p at decreasing
  rw [gammaAfter703, at170] at decreasing
  have numeric := numeric703 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 169 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 168)))
  rw [oldBefore170, at170, literal, oldAfter703, gammaAfter703]
  exact numeric
theorem numeric704 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 170 p
  rw [at170] at beforeRange
  have afterRange := bonus_range 149 (HazardPattern.afterPattern 10000 p (.walk 149))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ∧ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ≤ 2 at afterRange
  rw [gammaAfter704] at afterRange
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
theorem local704 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 149) + NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) + bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 149) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 170 p at decreasing
  rw [gammaAfter704, at170] at decreasing
  have numeric := numeric704 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149))
  rw [oldBefore170, at170, literal, oldAfter704, gammaAfter704]
  exact numeric
theorem numeric705 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 170 p
  rw [at170] at beforeRange
  have afterRange := bonus_range 147 (HazardPattern.afterPattern 10000 p (.walk 147))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ∧ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ≤ 2 at afterRange
  rw [gammaAfter705] at afterRange
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
theorem local705 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 147) + NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) + bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 147) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 170 p at decreasing
  rw [gammaAfter705, at170] at decreasing
  have numeric := numeric705 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147))
  rw [oldBefore170, at170, literal, oldAfter705, gammaAfter705]
  exact numeric
theorem numeric706 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 170 p
  rw [at170] at beforeRange
  have afterRange := bonus_range 193 (HazardPattern.afterPattern 10000 p (.walk 193))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ∧ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ≤ 2 at afterRange
  rw [gammaAfter706] at afterRange
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
theorem local706 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 193) + NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 193))) + bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 193) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 170 p at decreasing
  rw [gammaAfter706, at170] at decreasing
  have numeric := numeric706 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193))
  rw [oldBefore170, at170, literal, oldAfter706, gammaAfter706]
  exact numeric
theorem numeric707 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 170 p
  rw [at170] at beforeRange
  have afterRange := bonus_range 191 (HazardPattern.afterPattern 10000 p (.walk 191))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ∧ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ≤ 2 at afterRange
  rw [gammaAfter707] at afterRange
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
theorem local707 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 191) + NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 191))) + bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 191) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 170 p at decreasing
  rw [gammaAfter707, at170] at decreasing
  have numeric := numeric707 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191))
  rw [oldBefore170, at170, literal, oldAfter707, gammaAfter707]
  exact numeric
theorem numeric708 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 171 p
  rw [at171] at beforeRange
  have afterRange := bonus_range 149 (HazardPattern.afterPattern 10000 p (.walk 149))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ∧ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ≤ 2 at afterRange
  rw [gammaAfter708] at afterRange
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
theorem local708 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 171 p) :
    NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 171 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 149) + NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) + bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 149) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 171 p at decreasing
  rw [gammaAfter708, at171] at decreasing
  have numeric := numeric708 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149))
  rw [oldBefore171, at171, literal, oldAfter708, gammaAfter708]
  exact numeric
theorem numeric709 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 171 p
  rw [at171] at beforeRange
  have afterRange := bonus_range 149 (HazardPattern.afterPattern 10000 p (.push 149 (.stay 127)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 149 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 127))) ∧ bonus (HazardPattern.nextHero (.push 149 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 127))) ≤ 2 at afterRange
  rw [gammaAfter709] at afterRange
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
theorem local709 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 149 (HazardPattern.afterPattern 10000 p (.push 149 (.stay 127))) < bonus 171 p) :
    NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 171 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 149 (.stay 127)) + NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 149 (.stay 127)))) + bonus 149 (HazardPattern.afterPattern 10000 p (.push 149 (.stay 127))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 149 (.stay 127)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 149 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 127))) < bonus 171 p at decreasing
  rw [gammaAfter709, at171] at decreasing
  have numeric := numeric709 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 149 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 127)))
  rw [oldBefore171, at171, literal, oldAfter709, gammaAfter709]
  exact numeric
theorem numeric710 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 171 p
  rw [at171] at beforeRange
  have afterRange := bonus_range 193 (HazardPattern.afterPattern 10000 p (.walk 193))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ∧ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ≤ 2 at afterRange
  rw [gammaAfter710] at afterRange
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
theorem local710 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 171 p) :
    NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 171 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 193) + NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 193))) + bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 193) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 171 p at decreasing
  rw [gammaAfter710, at171] at decreasing
  have numeric := numeric710 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193))
  rw [oldBefore171, at171, literal, oldAfter710, gammaAfter710]
  exact numeric
theorem numeric711 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 171 p
  rw [at171] at beforeRange
  have afterRange := bonus_range 193 (HazardPattern.afterPattern 10000 p (.push 193 (.stay 215)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 193 (.stay 215))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 215))) ∧ bonus (HazardPattern.nextHero (.push 193 (.stay 215))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 215))) ≤ 2 at afterRange
  rw [gammaAfter711] at afterRange
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
theorem local711 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 193 (HazardPattern.afterPattern 10000 p (.push 193 (.stay 215))) < bonus 171 p) :
    NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 171 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 193 (.stay 215)) + NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 193 (.stay 215)))) + bonus 193 (HazardPattern.afterPattern 10000 p (.push 193 (.stay 215))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 193 (.stay 215)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 193 (.stay 215))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 215))) < bonus 171 p at decreasing
  rw [gammaAfter711, at171] at decreasing
  have numeric := numeric711 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 193 (.stay 215))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 215)))
  rw [oldBefore171, at171, literal, oldAfter711, gammaAfter711]
  exact numeric
theorem numeric712 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 171 p
  rw [at171] at beforeRange
  have afterRange := bonus_range 172 (HazardPattern.afterPattern 10000 p (.walk 172))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) ∧ bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) ≤ 2 at afterRange
  rw [gammaAfter712] at afterRange
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
theorem local712 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 172 (HazardPattern.afterPattern 10000 p (.walk 172)) < bonus 171 p) :
    NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 171 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 172) + NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 172))) + bonus 172 (HazardPattern.afterPattern 10000 p (.walk 172)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 172) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) < bonus 171 p at decreasing
  rw [gammaAfter712, at171] at decreasing
  have numeric := numeric712 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172))
  rw [oldBefore171, at171, literal, oldAfter712, gammaAfter712]
  exact numeric
theorem numeric713 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 171 p
  rw [at171] at beforeRange
  have afterRange := bonus_range 170 (HazardPattern.afterPattern 10000 p (.walk 170))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ∧ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ≤ 2 at afterRange
  rw [gammaAfter713] at afterRange
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
theorem local713 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 171 p) :
    NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 171 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 170) + NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 170))) + bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 170) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 171 p at decreasing
  rw [gammaAfter713, at171] at decreasing
  have numeric := numeric713 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170))
  rw [oldBefore171, at171, literal, oldAfter713, gammaAfter713]
  exact numeric
theorem numeric714 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 171 p
  rw [at171] at beforeRange
  have afterRange := bonus_range 170 (HazardPattern.afterPattern 10000 p (.push 170 (.stay 169)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 170 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 169))) ∧ bonus (HazardPattern.nextHero (.push 170 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 169))) ≤ 2 at afterRange
  rw [gammaAfter714] at afterRange
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
theorem local714 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 170 (HazardPattern.afterPattern 10000 p (.push 170 (.stay 169))) < bonus 171 p) :
    NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 171 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 170 (.stay 169)) + NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 170 (.stay 169)))) + bonus 170 (HazardPattern.afterPattern 10000 p (.push 170 (.stay 169))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 170 (.stay 169)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 170 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 169))) < bonus 171 p at decreasing
  rw [gammaAfter714, at171] at decreasing
  have numeric := numeric714 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 170 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 169)))
  rw [oldBefore171, at171, literal, oldAfter714, gammaAfter714]
  exact numeric
theorem numeric715 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 171 p
  rw [at171] at beforeRange
  have afterRange := bonus_range 150 (HazardPattern.afterPattern 10000 p (.walk 150))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) ∧ bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) ≤ 2 at afterRange
  rw [gammaAfter715] at afterRange
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
theorem local715 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 150 (HazardPattern.afterPattern 10000 p (.walk 150)) < bonus 171 p) :
    NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 171 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 150) + NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 150))) + bonus 150 (HazardPattern.afterPattern 10000 p (.walk 150)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 150) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) < bonus 171 p at decreasing
  rw [gammaAfter715, at171] at decreasing
  have numeric := numeric715 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150))
  rw [oldBefore171, at171, literal, oldAfter715, gammaAfter715]
  exact numeric
theorem numeric716 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 171 p
  rw [at171] at beforeRange
  have afterRange := bonus_range 148 (HazardPattern.afterPattern 10000 p (.walk 148))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ∧ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ≤ 2 at afterRange
  rw [gammaAfter716] at afterRange
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
theorem local716 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 171 p) :
    NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 171 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 148) + NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 148))) + bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 148) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 171 p at decreasing
  rw [gammaAfter716, at171] at decreasing
  have numeric := numeric716 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148))
  rw [oldBefore171, at171, literal, oldAfter716, gammaAfter716]
  exact numeric
theorem numeric717 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 171 p
  rw [at171] at beforeRange
  have afterRange := bonus_range 194 (HazardPattern.afterPattern 10000 p (.walk 194))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) ∧ bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) ≤ 2 at afterRange
  rw [gammaAfter717] at afterRange
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
theorem local717 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 194 (HazardPattern.afterPattern 10000 p (.walk 194)) < bonus 171 p) :
    NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 171 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 194) + NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 194))) + bonus 194 (HazardPattern.afterPattern 10000 p (.walk 194)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 194) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) < bonus 171 p at decreasing
  rw [gammaAfter717, at171] at decreasing
  have numeric := numeric717 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194))
  rw [oldBefore171, at171, literal, oldAfter717, gammaAfter717]
  exact numeric
theorem numeric718 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 171 p
  rw [at171] at beforeRange
  have afterRange := bonus_range 192 (HazardPattern.afterPattern 10000 p (.walk 192))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ∧ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ≤ 2 at afterRange
  rw [gammaAfter718] at afterRange
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
theorem local718 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 171 p) :
    NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 171 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 192) + NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 192))) + bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 192) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 171 p at decreasing
  rw [gammaAfter718, at171] at decreasing
  have numeric := numeric718 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192))
  rw [oldBefore171, at171, literal, oldAfter718, gammaAfter718]
  exact numeric
theorem numeric719 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 172 p
  rw [at172] at beforeRange
  have afterRange := bonus_range 150 (HazardPattern.afterPattern 10000 p (.walk 150))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) ∧ bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) ≤ 2 at afterRange
  rw [gammaAfter719] at afterRange
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
theorem local719 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 150 (HazardPattern.afterPattern 10000 p (.walk 150)) < bonus 172 p) :
    NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 172 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 150) + NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 150))) + bonus 150 (HazardPattern.afterPattern 10000 p (.walk 150)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 150) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) < bonus 172 p at decreasing
  rw [gammaAfter719, at172] at decreasing
  have numeric := numeric719 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150))
  rw [oldBefore172, at172, literal, oldAfter719, gammaAfter719]
  exact numeric
theorem numeric720 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 172 p
  rw [at172] at beforeRange
  have afterRange := bonus_range 150 (HazardPattern.afterPattern 10000 p (.push 150 (.stay 128)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 150 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 150 (.stay 128))) ∧ bonus (HazardPattern.nextHero (.push 150 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 150 (.stay 128))) ≤ 2 at afterRange
  rw [gammaAfter720] at afterRange
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
theorem local720 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 150 (HazardPattern.afterPattern 10000 p (.push 150 (.stay 128))) < bonus 172 p) :
    NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 172 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 150 (.stay 128)) + NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 150 (.stay 128)))) + bonus 150 (HazardPattern.afterPattern 10000 p (.push 150 (.stay 128))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 150 (.stay 128)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 150 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 150 (.stay 128))) < bonus 172 p at decreasing
  rw [gammaAfter720, at172] at decreasing
  have numeric := numeric720 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 150 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 150 (.stay 128)))
  rw [oldBefore172, at172, literal, oldAfter720, gammaAfter720]
  exact numeric
theorem numeric721 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 172 p
  rw [at172] at beforeRange
  have afterRange := bonus_range 194 (HazardPattern.afterPattern 10000 p (.walk 194))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) ∧ bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) ≤ 2 at afterRange
  rw [gammaAfter721] at afterRange
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
theorem local721 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 194 (HazardPattern.afterPattern 10000 p (.walk 194)) < bonus 172 p) :
    NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 172 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 194) + NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 194))) + bonus 194 (HazardPattern.afterPattern 10000 p (.walk 194)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 194) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) < bonus 172 p at decreasing
  rw [gammaAfter721, at172] at decreasing
  have numeric := numeric721 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194))
  rw [oldBefore172, at172, literal, oldAfter721, gammaAfter721]
  exact numeric
theorem numeric722 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 172 p
  rw [at172] at beforeRange
  have afterRange := bonus_range 194 (HazardPattern.afterPattern 10000 p (.push 194 (.stay 216)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 194 (.stay 216))) (HazardPattern.afterPattern 10000 p (.push 194 (.stay 216))) ∧ bonus (HazardPattern.nextHero (.push 194 (.stay 216))) (HazardPattern.afterPattern 10000 p (.push 194 (.stay 216))) ≤ 2 at afterRange
  rw [gammaAfter722] at afterRange
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
theorem local722 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 194 (HazardPattern.afterPattern 10000 p (.push 194 (.stay 216))) < bonus 172 p) :
    NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 172 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 194 (.stay 216)) + NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 194 (.stay 216)))) + bonus 194 (HazardPattern.afterPattern 10000 p (.push 194 (.stay 216))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 194 (.stay 216)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 194 (.stay 216))) (HazardPattern.afterPattern 10000 p (.push 194 (.stay 216))) < bonus 172 p at decreasing
  rw [gammaAfter722, at172] at decreasing
  have numeric := numeric722 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 194 (.stay 216))) (HazardPattern.afterPattern 10000 p (.push 194 (.stay 216)))
  rw [oldBefore172, at172, literal, oldAfter722, gammaAfter722]
  exact numeric
theorem numeric723 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 172 p
  rw [at172] at beforeRange
  have afterRange := bonus_range 171 (HazardPattern.afterPattern 10000 p (.walk 171))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ∧ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ≤ 2 at afterRange
  rw [gammaAfter723] at afterRange
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
theorem local723 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 172 p) :
    NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 172 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 171) + NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 171))) + bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 171) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 172 p at decreasing
  rw [gammaAfter723, at172] at decreasing
  have numeric := numeric723 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171))
  rw [oldBefore172, at172, literal, oldAfter723, gammaAfter723]
  exact numeric
theorem numeric724 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 172 p
  rw [at172] at beforeRange
  have afterRange := bonus_range 171 (HazardPattern.afterPattern 10000 p (.push 171 (.stay 170)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 171 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 170))) ∧ bonus (HazardPattern.nextHero (.push 171 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 170))) ≤ 2 at afterRange
  rw [gammaAfter724] at afterRange
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
theorem local724 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 171 (HazardPattern.afterPattern 10000 p (.push 171 (.stay 170))) < bonus 172 p) :
    NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 172 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 171 (.stay 170)) + NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 171 (.stay 170)))) + bonus 171 (HazardPattern.afterPattern 10000 p (.push 171 (.stay 170))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 171 (.stay 170)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 171 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 170))) < bonus 172 p at decreasing
  rw [gammaAfter724, at172] at decreasing
  have numeric := numeric724 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 171 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 170)))
  rw [oldBefore172, at172, literal, oldAfter724, gammaAfter724]
  exact numeric
theorem numeric725 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 172 p
  rw [at172] at beforeRange
  have afterRange := bonus_range 149 (HazardPattern.afterPattern 10000 p (.walk 149))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ∧ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ≤ 2 at afterRange
  rw [gammaAfter725] at afterRange
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
theorem local725 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 172 p) :
    NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 172 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 149) + NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) + bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 149) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 172 p at decreasing
  rw [gammaAfter725, at172] at decreasing
  have numeric := numeric725 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149))
  rw [oldBefore172, at172, literal, oldAfter725, gammaAfter725]
  exact numeric
theorem numeric726 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 172 p
  rw [at172] at beforeRange
  have afterRange := bonus_range 193 (HazardPattern.afterPattern 10000 p (.walk 193))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ∧ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ≤ 2 at afterRange
  rw [gammaAfter726] at afterRange
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
theorem local726 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 172 p) :
    NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 172 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 193) + NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 193))) + bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 193) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 172 p at decreasing
  rw [gammaAfter726, at172] at decreasing
  have numeric := numeric726 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193))
  rw [oldBefore172, at172, literal, oldAfter726, gammaAfter726]
  exact numeric
theorem numeric727 (p : Pattern) (guard : d132764 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 177 p
  rw [at177] at beforeRange
  have afterRange := bonus_range 155 (HazardPattern.afterPattern 10000 p (.walk 155))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) ∧ bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) ≤ 2 at afterRange
  rw [gammaAfter727] at afterRange
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
theorem local727 (p : Pattern) (guard : d132764 p = 1)
    (decreasing : bonus 155 (HazardPattern.afterPattern 10000 p (.walk 155)) < bonus 177 p) :
    NetHack.Sokoban22Refined85.bonus 177 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 177 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 155) + NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 155))) + bonus 155 (HazardPattern.afterPattern 10000 p (.walk 155)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 155) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) < bonus 177 p at decreasing
  rw [gammaAfter727, at177] at decreasing
  have numeric := numeric727 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155))
  rw [oldBefore177, at177, literal, oldAfter727, gammaAfter727]
  exact numeric
theorem numeric728 (p : Pattern) (guard : d102598 p = 1) (decreasing : d0 p < d5849 p) :
    d47866 p + d5849 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 177 p
  rw [at177] at beforeRange
  have afterRange := bonus_range 155 (HazardPattern.afterPattern 10000 p (.push 155 (.stay 133)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 155 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 155 (.stay 133))) ∧ bonus (HazardPattern.nextHero (.push 155 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 155 (.stay 133))) ≤ 2 at afterRange
  rw [gammaAfter728] at afterRange
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
theorem local728 (p : Pattern) (guard : d102598 p = 1)
    (decreasing : bonus 155 (HazardPattern.afterPattern 10000 p (.push 155 (.stay 133))) < bonus 177 p) :
    NetHack.Sokoban22Refined85.bonus 177 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 177 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 155 (.stay 133)) + NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 155 (.stay 133)))) + bonus 155 (HazardPattern.afterPattern 10000 p (.push 155 (.stay 133))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 155 (.stay 133)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 155 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 155 (.stay 133))) < bonus 177 p at decreasing
  rw [gammaAfter728, at177] at decreasing
  have numeric := numeric728 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 155 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 155 (.stay 133)))
  rw [oldBefore177, at177, literal, oldAfter728, gammaAfter728]
  exact numeric
theorem numeric729 (p : Pattern) (guard : d194333 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 177 p
  rw [at177] at beforeRange
  have afterRange := bonus_range 199 (HazardPattern.afterPattern 10000 p (.walk 199))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 199)) (HazardPattern.afterPattern 10000 p (.walk 199)) ∧ bonus (HazardPattern.nextHero (.walk 199)) (HazardPattern.afterPattern 10000 p (.walk 199)) ≤ 2 at afterRange
  rw [gammaAfter729] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro45720 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro45721 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro45721 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local729 (p : Pattern) (guard : d194333 p = 1)
    (decreasing : bonus 199 (HazardPattern.afterPattern 10000 p (.walk 199)) < bonus 177 p) :
    NetHack.Sokoban22Refined85.bonus 177 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 177 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 199) + NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 199))) + bonus 199 (HazardPattern.afterPattern 10000 p (.walk 199)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 199) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 199)) (HazardPattern.afterPattern 10000 p (.walk 199)) < bonus 177 p at decreasing
  rw [gammaAfter729, at177] at decreasing
  have numeric := numeric729 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 199)) (HazardPattern.afterPattern 10000 p (.walk 199))
  rw [oldBefore177, at177, literal, oldAfter729, gammaAfter729]
  exact numeric
theorem numeric730 (p : Pattern) (guard : d139752 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 177 p
  rw [at177] at beforeRange
  have afterRange := bonus_range 156 (HazardPattern.afterPattern 10000 p (.walk 156))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) ∧ bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) ≤ 2 at afterRange
  rw [gammaAfter730] at afterRange
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
theorem local730 (p : Pattern) (guard : d139752 p = 1)
    (decreasing : bonus 156 (HazardPattern.afterPattern 10000 p (.walk 156)) < bonus 177 p) :
    NetHack.Sokoban22Refined85.bonus 177 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 177 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 156) + NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 156))) + bonus 156 (HazardPattern.afterPattern 10000 p (.walk 156)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 156) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) < bonus 177 p at decreasing
  rw [gammaAfter730, at177] at decreasing
  have numeric := numeric730 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156))
  rw [oldBefore177, at177, literal, oldAfter730, gammaAfter730]
  exact numeric
theorem numeric731 (p : Pattern) (guard : d194337 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 177 p
  rw [at177] at beforeRange
  have afterRange := bonus_range 200 (HazardPattern.afterPattern 10000 p (.walk 200))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) ∧ bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) ≤ 2 at afterRange
  rw [gammaAfter731] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro45722 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro45723 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro45723 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local731 (p : Pattern) (guard : d194337 p = 1)
    (decreasing : bonus 200 (HazardPattern.afterPattern 10000 p (.walk 200)) < bonus 177 p) :
    NetHack.Sokoban22Refined85.bonus 177 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 177 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 200) + NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 200))) + bonus 200 (HazardPattern.afterPattern 10000 p (.walk 200)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 200) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) < bonus 177 p at decreasing
  rw [gammaAfter731, at177] at decreasing
  have numeric := numeric731 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200))
  rw [oldBefore177, at177, literal, oldAfter731, gammaAfter731]
  exact numeric
theorem numeric732 (p : Pattern) (guard : d146836 p = 1) (decreasing : d13979 p < d23134 p) :
    d47866 p + d23134 p ≤ (0 : Int) + d47866 p + d13979 p := by
  have beforeRange := bonus_range 180 p
  rw [at180] at beforeRange
  have afterRange := bonus_range 158 (HazardPattern.afterPattern 10000 p (.walk 158))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) ∧ bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) ≤ 2 at afterRange
  rw [gammaAfter732] at afterRange
  have possibilities : (d23134 p = 1 ∧ d13979 p = 0) ∨ (d23134 p = 2 ∧ d13979 p = 0) ∨ (d23134 p = 2 ∧ d13979 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro13358 p pair.1
    have afterEq := eqIntro8488 p pair.2
    have combined := andIntro46019 p guard beforeEq
    have complete := andIntro46330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro8488 p pair.2
    have combined := andIntro46368 p guard beforeEq
    have complete := andIntro46415 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro8624 p pair.2
    have combined := andIntro46368 p guard beforeEq
    have complete := andIntro46459 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local732 (p : Pattern) (guard : d146836 p = 1)
    (decreasing : bonus 158 (HazardPattern.afterPattern 10000 p (.walk 158)) < bonus 180 p) :
    NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 180 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 158) + NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 158))) + bonus 158 (HazardPattern.afterPattern 10000 p (.walk 158)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 158) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) < bonus 180 p at decreasing
  rw [gammaAfter732, at180] at decreasing
  have numeric := numeric732 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158))
  rw [oldBefore180, at180, literal, oldAfter732, gammaAfter732]
  exact numeric
theorem numeric733 (p : Pattern) (guard : d116753 p = 1) (decreasing : d195382 p < d23134 p) :
    d47866 p + d23134 p ≤ (2 : Int) + d47866 p + d195382 p := by
  have beforeRange := bonus_range 180 p
  rw [at180] at beforeRange
  have afterRange := bonus_range 158 (HazardPattern.afterPattern 10000 p (.push 158 (.stay 136)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 158 (.stay 136))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 136))) ∧ bonus (HazardPattern.nextHero (.push 158 (.stay 136))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 136))) ≤ 2 at afterRange
  rw [gammaAfter733] at afterRange
  have possibilities : (d23134 p = 1 ∧ d195382 p = 0) ∨ (d23134 p = 2 ∧ d195382 p = 0) ∨ (d23134 p = 2 ∧ d195382 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro13358 p pair.1
    have afterEq := eqIntro18620 p pair.2
    have combined := andIntro46751 p guard beforeEq
    have complete := andIntro46973 p afterEq combined
    have bound := compare28858 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro18620 p pair.2
    have combined := andIntro47011 p guard beforeEq
    have complete := andIntro47055 p afterEq combined
    have bound := compare28859 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro18683 p pair.2
    have combined := andIntro47011 p guard beforeEq
    have complete := andIntro47099 p combined afterEq
    have bound := compare10066 p complete
    omega
theorem local733 (p : Pattern) (guard : d116753 p = 1)
    (decreasing : bonus 158 (HazardPattern.afterPattern 10000 p (.push 158 (.stay 136))) < bonus 180 p) :
    NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 180 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 158 (.stay 136)) + NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 158 (.stay 136)))) + bonus 158 (HazardPattern.afterPattern 10000 p (.push 158 (.stay 136))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 158 (.stay 136)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 158 (.stay 136))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 136))) < bonus 180 p at decreasing
  rw [gammaAfter733, at180] at decreasing
  have numeric := numeric733 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 158 (.stay 136))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 136)))
  rw [oldBefore180, at180, literal, oldAfter733, gammaAfter733]
  exact numeric
theorem numeric734 (p : Pattern) (guard : d198467 p = 1) (decreasing : d27480 p < d23134 p) :
    d47866 p + d23134 p ≤ (0 : Int) + d47866 p + d27480 p := by
  have beforeRange := bonus_range 180 p
  rw [at180] at beforeRange
  have afterRange := bonus_range 202 (HazardPattern.afterPattern 10000 p (.walk 202))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) ∧ bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) ≤ 2 at afterRange
  rw [gammaAfter734] at afterRange
  have possibilities : (d23134 p = 1 ∧ d27480 p = 0) ∨ (d23134 p = 2 ∧ d27480 p = 0) ∨ (d23134 p = 2 ∧ d27480 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro13358 p pair.1
    have afterEq := eqIntro19116 p pair.2
    have combined := andIntro47427 p beforeEq guard
    have complete := andIntro47750 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro19116 p pair.2
    have combined := andIntro47788 p beforeEq guard
    have complete := andIntro47837 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro19271 p pair.2
    have combined := andIntro47788 p beforeEq guard
    have complete := andIntro47886 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local734 (p : Pattern) (guard : d198467 p = 1)
    (decreasing : bonus 202 (HazardPattern.afterPattern 10000 p (.walk 202)) < bonus 180 p) :
    NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 180 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 202) + NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 202))) + bonus 202 (HazardPattern.afterPattern 10000 p (.walk 202)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 202) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) < bonus 180 p at decreasing
  rw [gammaAfter734, at180] at decreasing
  have numeric := numeric734 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202))
  rw [oldBefore180, at180, literal, oldAfter734, gammaAfter734]
  exact numeric
theorem numeric735 (p : Pattern) (guard : d202307 p = 1) (decreasing : d204364 p < d23134 p) :
    d47866 p + d23134 p ≤ (0 : Int) + d47866 p + d204364 p := by
  have beforeRange := bonus_range 180 p
  rw [at180] at beforeRange
  have afterRange := bonus_range 202 (HazardPattern.afterPattern 10000 p (.push 202 (.stay 224)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 202 (.stay 224))) (HazardPattern.afterPattern 10000 p (.push 202 (.stay 224))) ∧ bonus (HazardPattern.nextHero (.push 202 (.stay 224))) (HazardPattern.afterPattern 10000 p (.push 202 (.stay 224))) ≤ 2 at afterRange
  rw [gammaAfter735] at afterRange
  have possibilities : (d23134 p = 1 ∧ d204364 p = 0) ∨ (d23134 p = 2 ∧ d204364 p = 0) ∨ (d23134 p = 2 ∧ d204364 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro13358 p pair.1
    have afterEq := eqIntro19674 p pair.2
    have combined := andIntro48273 p beforeEq guard
    have complete := andIntro48587 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro19674 p pair.2
    have combined := andIntro48626 p beforeEq guard
    have complete := andIntro48673 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro19828 p pair.2
    have combined := andIntro48626 p beforeEq guard
    have complete := andIntro48717 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local735 (p : Pattern) (guard : d202307 p = 1)
    (decreasing : bonus 202 (HazardPattern.afterPattern 10000 p (.push 202 (.stay 224))) < bonus 180 p) :
    NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 180 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 202 (.stay 224)) + NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 202 (.stay 224)))) + bonus 202 (HazardPattern.afterPattern 10000 p (.push 202 (.stay 224))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 202 (.stay 224)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 202 (.stay 224))) (HazardPattern.afterPattern 10000 p (.push 202 (.stay 224))) < bonus 180 p at decreasing
  rw [gammaAfter735, at180] at decreasing
  have numeric := numeric735 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 202 (.stay 224))) (HazardPattern.afterPattern 10000 p (.push 202 (.stay 224)))
  rw [oldBefore180, at180, literal, oldAfter735, gammaAfter735]
  exact numeric
theorem numeric736 (p : Pattern) (guard : d207963 p = 1) (decreasing : d17560 p < d23134 p) :
    d47866 p + d23134 p ≤ (0 : Int) + d47866 p + d17560 p := by
  have beforeRange := bonus_range 180 p
  rw [at180] at beforeRange
  have afterRange := bonus_range 181 (HazardPattern.afterPattern 10000 p (.walk 181))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ∧ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ≤ 2 at afterRange
  rw [gammaAfter736] at afterRange
  have possibilities : (d23134 p = 1 ∧ d17560 p = 0) ∨ (d23134 p = 2 ∧ d17560 p = 0) ∨ (d23134 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro13358 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro48718 p beforeEq guard
    have complete := andIntro49018 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro49019 p beforeEq guard
    have complete := andIntro49069 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro49019 p beforeEq guard
    have complete := andIntro49113 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local736 (p : Pattern) (guard : d207963 p = 1)
    (decreasing : bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 180 p) :
    NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 180 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 181) + NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 181))) + bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 181) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 180 p at decreasing
  rw [gammaAfter736, at180] at decreasing
  have numeric := numeric736 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181))
  rw [oldBefore180, at180, literal, oldAfter736, gammaAfter736]
  exact numeric
theorem numeric737 (p : Pattern) (guard : d207966 p = 1) (decreasing : d0 p < d23134 p) :
    d47866 p + d23134 p ≤ (0 : Int) + d208030 p + d0 p := by
  have beforeRange := bonus_range 180 p
  rw [at180] at beforeRange
  have afterRange := bonus_range 181 (HazardPattern.afterPattern 10000 p (.push 181 (.stay 182)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 181 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 181 (.stay 182))) ∧ bonus (HazardPattern.nextHero (.push 181 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 181 (.stay 182))) ≤ 2 at afterRange
  rw [gammaAfter737] at afterRange
  have possibilities : (d23134 p = 1 ∧ d0 p = 0) ∨ (d23134 p = 2 ∧ d0 p = 0) ∨ (d23134 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro13358 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro49118 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare28860 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro49123 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare28861 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro49123 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare28860 p complete
    omega
theorem local737 (p : Pattern) (guard : d207966 p = 1)
    (decreasing : bonus 181 (HazardPattern.afterPattern 10000 p (.push 181 (.stay 182))) < bonus 180 p) :
    NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 180 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 181 (.stay 182)) + NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 181 (.stay 182)))) + bonus 181 (HazardPattern.afterPattern 10000 p (.push 181 (.stay 182))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 181 (.stay 182)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 181 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 181 (.stay 182))) < bonus 180 p at decreasing
  rw [gammaAfter737, at180] at decreasing
  have numeric := numeric737 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 181 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 181 (.stay 182)))
  rw [oldBefore180, at180, literal, oldAfter737, gammaAfter737]
  exact numeric
theorem numeric738 (p : Pattern) (guard : d169397 p = 1) (decreasing : d15965 p < d23134 p) :
    d47866 p + d23134 p ≤ (0 : Int) + d47866 p + d15965 p := by
  have beforeRange := bonus_range 180 p
  rw [at180] at beforeRange
  have afterRange := bonus_range 159 (HazardPattern.afterPattern 10000 p (.walk 159))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ∧ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ≤ 2 at afterRange
  rw [gammaAfter738] at afterRange
  have possibilities : (d23134 p = 1 ∧ d15965 p = 0) ∨ (d23134 p = 2 ∧ d15965 p = 0) ∨ (d23134 p = 2 ∧ d15965 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro13358 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro49407 p beforeEq guard
    have complete := andIntro49687 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro49725 p guard beforeEq
    have complete := andIntro49775 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro9862 p pair.2
    have combined := andIntro49725 p guard beforeEq
    have complete := andIntro49819 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local738 (p : Pattern) (guard : d169397 p = 1)
    (decreasing : bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 180 p) :
    NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 180 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 159) + NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 159))) + bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 159) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 180 p at decreasing
  rw [gammaAfter738, at180] at decreasing
  have numeric := numeric738 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159))
  rw [oldBefore180, at180, literal, oldAfter738, gammaAfter738]
  exact numeric
theorem numeric739 (p : Pattern) (guard : d146837 p = 1) (decreasing : d12224 p < d23134 p) :
    d47866 p + d23134 p ≤ (0 : Int) + d47866 p + d12224 p := by
  have beforeRange := bonus_range 180 p
  rw [at180] at beforeRange
  have afterRange := bonus_range 157 (HazardPattern.afterPattern 10000 p (.walk 157))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) ∧ bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) ≤ 2 at afterRange
  rw [gammaAfter739] at afterRange
  have possibilities : (d23134 p = 1 ∧ d12224 p = 0) ∨ (d23134 p = 2 ∧ d12224 p = 0) ∨ (d23134 p = 2 ∧ d12224 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro13358 p pair.1
    have afterEq := eqIntro7713 p pair.2
    have combined := andIntro50063 p guard beforeEq
    have complete := andIntro50338 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro7713 p pair.2
    have combined := andIntro50376 p guard beforeEq
    have complete := andIntro50420 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro7817 p pair.2
    have combined := andIntro50376 p guard beforeEq
    have complete := andIntro50464 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local739 (p : Pattern) (guard : d146837 p = 1)
    (decreasing : bonus 157 (HazardPattern.afterPattern 10000 p (.walk 157)) < bonus 180 p) :
    NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 180 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 157) + NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 157))) + bonus 157 (HazardPattern.afterPattern 10000 p (.walk 157)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 157) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) < bonus 180 p at decreasing
  rw [gammaAfter739, at180] at decreasing
  have numeric := numeric739 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157))
  rw [oldBefore180, at180, literal, oldAfter739, gammaAfter739]
  exact numeric
theorem numeric740 (p : Pattern) (guard : d208035 p = 1) (decreasing : d25101 p < d23134 p) :
    d47866 p + d23134 p ≤ (0 : Int) + d47866 p + d25101 p := by
  have beforeRange := bonus_range 180 p
  rw [at180] at beforeRange
  have afterRange := bonus_range 201 (HazardPattern.afterPattern 10000 p (.walk 201))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) ∧ bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) ≤ 2 at afterRange
  rw [gammaAfter740] at afterRange
  have possibilities : (d23134 p = 1 ∧ d25101 p = 0) ∨ (d23134 p = 2 ∧ d25101 p = 0) ∨ (d23134 p = 2 ∧ d25101 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro13358 p pair.1
    have afterEq := eqIntro20211 p pair.2
    have combined := andIntro50795 p beforeEq guard
    have complete := andIntro51097 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro20211 p pair.2
    have combined := andIntro51135 p beforeEq guard
    have complete := andIntro51184 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro18476 p pair.1
    have afterEq := eqIntro20354 p pair.2
    have combined := andIntro51135 p beforeEq guard
    have complete := andIntro51233 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local740 (p : Pattern) (guard : d208035 p = 1)
    (decreasing : bonus 201 (HazardPattern.afterPattern 10000 p (.walk 201)) < bonus 180 p) :
    NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 180 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 201) + NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 201))) + bonus 201 (HazardPattern.afterPattern 10000 p (.walk 201)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 201) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) < bonus 180 p at decreasing
  rw [gammaAfter740, at180] at decreasing
  have numeric := numeric740 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201))
  rw [oldBefore180, at180, literal, oldAfter740, gammaAfter740]
  exact numeric
theorem numeric741 (p : Pattern) (guard : d163444 p = 1) (decreasing : d15965 p < d17560 p) :
    d47866 p + d17560 p ≤ (0 : Int) + d47866 p + d15965 p := by
  have beforeRange := bonus_range 181 p
  rw [at181] at beforeRange
  have afterRange := bonus_range 159 (HazardPattern.afterPattern 10000 p (.walk 159))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ∧ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ≤ 2 at afterRange
  rw [gammaAfter741] at afterRange
  have possibilities : (d17560 p = 1 ∧ d15965 p = 0) ∨ (d17560 p = 2 ∧ d15965 p = 0) ∨ (d17560 p = 2 ∧ d15965 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro51517 p beforeEq guard
    have complete := andIntro40006 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro51555 p guard beforeEq
    have complete := andIntro40094 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro9862 p pair.2
    have combined := andIntro51555 p guard beforeEq
    have complete := andIntro40138 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local741 (p : Pattern) (guard : d163444 p = 1)
    (decreasing : bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 159) + NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 159))) + bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 159) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 181 p at decreasing
  rw [gammaAfter741, at181] at decreasing
  have numeric := numeric741 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159))
  rw [oldBefore181, at181, literal, oldAfter741, gammaAfter741]
  exact numeric
theorem numeric742 (p : Pattern) (guard : d211412 p = 1) (decreasing : d17560 p < d17560 p) :
    d47866 p + d17560 p ≤ (0 : Int) + d49280 p + d17560 p := by
  have beforeRange := bonus_range 181 p
  rw [at181] at beforeRange
  have afterRange := bonus_range 182 (HazardPattern.afterPattern 10000 p (.walk 182))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) ∧ bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) ≤ 2 at afterRange
  rw [gammaAfter742] at afterRange
  have possibilities : (d17560 p = 1 ∧ d17560 p = 0) ∨ (d17560 p = 2 ∧ d17560 p = 0) ∨ (d17560 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro51556 p beforeEq guard
    have complete := andIntro38077 p afterEq combined
    have bound := compare13660 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro51557 p beforeEq guard
    have complete := andIntro38128 p afterEq combined
    have bound := compare13661 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro51557 p beforeEq guard
    have complete := andIntro38172 p afterEq combined
    have bound := compare13660 p complete
    omega
theorem local742 (p : Pattern) (guard : d211412 p = 1)
    (decreasing : bonus 182 (HazardPattern.afterPattern 10000 p (.walk 182)) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 182) + NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 182))) + bonus 182 (HazardPattern.afterPattern 10000 p (.walk 182)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 182) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) < bonus 181 p at decreasing
  rw [gammaAfter742, at181] at decreasing
  have numeric := numeric742 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182))
  rw [oldBefore181, at181, literal, oldAfter742, gammaAfter742]
  exact numeric
theorem numeric743 (p : Pattern) (guard : d207963 p = 1) (decreasing : d23134 p < d17560 p) :
    d47866 p + d17560 p ≤ (0 : Int) + d47866 p + d23134 p := by
  have beforeRange := bonus_range 181 p
  rw [at181] at beforeRange
  have afterRange := bonus_range 180 (HazardPattern.afterPattern 10000 p (.walk 180))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) ∧ bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) ≤ 2 at afterRange
  rw [gammaAfter743] at afterRange
  have possibilities : (d17560 p = 1 ∧ d23134 p = 0) ∨ (d17560 p = 2 ∧ d23134 p = 0) ∨ (d17560 p = 2 ∧ d23134 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro13202 p pair.2
    have combined := andIntro51866 p beforeEq guard
    have complete := andIntro52150 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro13202 p pair.2
    have combined := andIntro52188 p beforeEq guard
    have complete := andIntro52238 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro13358 p pair.2
    have combined := andIntro52188 p beforeEq guard
    have complete := andIntro52282 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local743 (p : Pattern) (guard : d207963 p = 1)
    (decreasing : bonus 180 (HazardPattern.afterPattern 10000 p (.walk 180)) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 180) + NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 180))) + bonus 180 (HazardPattern.afterPattern 10000 p (.walk 180)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 180) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) < bonus 181 p at decreasing
  rw [gammaAfter743, at181] at decreasing
  have numeric := numeric743 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180))
  rw [oldBefore181, at181, literal, oldAfter743, gammaAfter743]
  exact numeric
theorem numeric744 (p : Pattern) (guard : d180907 p = 1) (decreasing : d17560 p < d17560 p) :
    d47866 p + d17560 p ≤ (0 : Int) + d48388 p + d17560 p := by
  have beforeRange := bonus_range 181 p
  rw [at181] at beforeRange
  have afterRange := bonus_range 160 (HazardPattern.afterPattern 10000 p (.walk 160))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) ∧ bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) ≤ 2 at afterRange
  rw [gammaAfter744] at afterRange
  have possibilities : (d17560 p = 1 ∧ d17560 p = 0) ∨ (d17560 p = 2 ∧ d17560 p = 0) ∨ (d17560 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro40824 p beforeEq guard
    have complete := andIntro38077 p afterEq combined
    have bound := compare13654 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro40825 p beforeEq guard
    have complete := andIntro38128 p afterEq combined
    have bound := compare13655 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro40825 p beforeEq guard
    have complete := andIntro38172 p afterEq combined
    have bound := compare13654 p complete
    omega
theorem local744 (p : Pattern) (guard : d180907 p = 1)
    (decreasing : bonus 160 (HazardPattern.afterPattern 10000 p (.walk 160)) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 160) + NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 160))) + bonus 160 (HazardPattern.afterPattern 10000 p (.walk 160)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 160) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) < bonus 181 p at decreasing
  rw [gammaAfter744, at181] at decreasing
  have numeric := numeric744 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160))
  rw [oldBefore181, at181, literal, oldAfter744, gammaAfter744]
  exact numeric
theorem numeric745 (p : Pattern) (guard : d162095 p = 1) (decreasing : d13979 p < d17560 p) :
    d47866 p + d17560 p ≤ (0 : Int) + d47866 p + d13979 p := by
  have beforeRange := bonus_range 181 p
  rw [at181] at beforeRange
  have afterRange := bonus_range 158 (HazardPattern.afterPattern 10000 p (.walk 158))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) ∧ bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) ≤ 2 at afterRange
  rw [gammaAfter745] at afterRange
  have possibilities : (d17560 p = 1 ∧ d13979 p = 0) ∨ (d17560 p = 2 ∧ d13979 p = 0) ∨ (d17560 p = 2 ∧ d13979 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro8488 p pair.2
    have combined := andIntro52578 p beforeEq guard
    have complete := andIntro52827 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro8488 p pair.2
    have combined := andIntro52865 p guard beforeEq
    have complete := andIntro52912 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro8624 p pair.2
    have combined := andIntro52865 p guard beforeEq
    have complete := andIntro52956 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local745 (p : Pattern) (guard : d162095 p = 1)
    (decreasing : bonus 158 (HazardPattern.afterPattern 10000 p (.walk 158)) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 158) + NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 158))) + bonus 158 (HazardPattern.afterPattern 10000 p (.walk 158)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 158) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) < bonus 181 p at decreasing
  rw [gammaAfter745, at181] at decreasing
  have numeric := numeric745 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158))
  rw [oldBefore181, at181, literal, oldAfter745, gammaAfter745]
  exact numeric
theorem numeric746 (p : Pattern) (guard : d211416 p = 1) (decreasing : d28738 p < d17560 p) :
    d47866 p + d17560 p ≤ (0 : Int) + d49782 p + d28738 p := by
  have beforeRange := bonus_range 181 p
  rw [at181] at beforeRange
  have afterRange := bonus_range 204 (HazardPattern.afterPattern 10000 p (.walk 204))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) ∧ bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) ≤ 2 at afterRange
  rw [gammaAfter746] at afterRange
  have possibilities : (d17560 p = 1 ∧ d28738 p = 0) ∨ (d17560 p = 2 ∧ d28738 p = 0) ∨ (d17560 p = 2 ∧ d28738 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro20553 p pair.2
    have combined := andIntro53101 p beforeEq guard
    have complete := andIntro53246 p afterEq combined
    have bound := compare28862 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro20553 p pair.2
    have combined := andIntro53266 p beforeEq guard
    have complete := andIntro53290 p afterEq combined
    have bound := compare28863 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro20627 p pair.2
    have combined := andIntro53266 p beforeEq guard
    have complete := andIntro53310 p afterEq combined
    have bound := compare28862 p complete
    omega
theorem local746 (p : Pattern) (guard : d211416 p = 1)
    (decreasing : bonus 204 (HazardPattern.afterPattern 10000 p (.walk 204)) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 204) + NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 204))) + bonus 204 (HazardPattern.afterPattern 10000 p (.walk 204)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 204) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) < bonus 181 p at decreasing
  rw [gammaAfter746, at181] at decreasing
  have numeric := numeric746 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204))
  rw [oldBefore181, at181, literal, oldAfter746, gammaAfter746]
  exact numeric
theorem numeric747 (p : Pattern) (guard : d212559 p = 1) (decreasing : d27480 p < d17560 p) :
    d47866 p + d17560 p ≤ (0 : Int) + d47866 p + d27480 p := by
  have beforeRange := bonus_range 181 p
  rw [at181] at beforeRange
  have afterRange := bonus_range 202 (HazardPattern.afterPattern 10000 p (.walk 202))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) ∧ bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) ≤ 2 at afterRange
  rw [gammaAfter747] at afterRange
  have possibilities : (d17560 p = 1 ∧ d27480 p = 0) ∨ (d17560 p = 2 ∧ d27480 p = 0) ∨ (d17560 p = 2 ∧ d27480 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro19116 p pair.2
    have combined := andIntro53649 p beforeEq guard
    have complete := andIntro47750 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro19116 p pair.2
    have combined := andIntro53687 p beforeEq guard
    have complete := andIntro47837 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro19271 p pair.2
    have combined := andIntro53687 p beforeEq guard
    have complete := andIntro47886 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local747 (p : Pattern) (guard : d212559 p = 1)
    (decreasing : bonus 202 (HazardPattern.afterPattern 10000 p (.walk 202)) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 202) + NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 202))) + bonus 202 (HazardPattern.afterPattern 10000 p (.walk 202)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 202) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) < bonus 181 p at decreasing
  rw [gammaAfter747, at181] at decreasing
  have numeric := numeric747 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202))
  rw [oldBefore181, at181, literal, oldAfter747, gammaAfter747]
  exact numeric
theorem numeric748 (p : Pattern) (guard : d169389 p = 1) (decreasing : d17560 p < d17560 p) :
    d49280 p + d17560 p ≤ (0 : Int) + d48388 p + d17560 p := by
  have beforeRange := bonus_range 182 p
  rw [at182] at beforeRange
  have afterRange := bonus_range 160 (HazardPattern.afterPattern 10000 p (.walk 160))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) ∧ bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) ≤ 2 at afterRange
  rw [gammaAfter748] at afterRange
  have possibilities : (d17560 p = 1 ∧ d17560 p = 0) ∨ (d17560 p = 2 ∧ d17560 p = 0) ∨ (d17560 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro37859 p beforeEq guard
    have complete := andIntro38077 p afterEq combined
    have bound := compare28864 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro38078 p guard beforeEq
    have complete := andIntro38128 p afterEq combined
    have bound := compare28865 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro38078 p guard beforeEq
    have complete := andIntro38172 p afterEq combined
    have bound := compare28864 p complete
    omega
theorem local748 (p : Pattern) (guard : d169389 p = 1)
    (decreasing : bonus 160 (HazardPattern.afterPattern 10000 p (.walk 160)) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 160) + NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 160))) + bonus 160 (HazardPattern.afterPattern 10000 p (.walk 160)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 160) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) < bonus 182 p at decreasing
  rw [gammaAfter748, at182] at decreasing
  have numeric := numeric748 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160))
  rw [oldBefore182, at182, literal, oldAfter748, gammaAfter748]
  exact numeric
theorem numeric749 (p : Pattern) (guard : d128487 p = 1) (decreasing : d214541 p < d17560 p) :
    d49280 p + d17560 p ≤ (2 : Int) + d212576 p + d214541 p := by
  have beforeRange := bonus_range 182 p
  rw [at182] at beforeRange
  have afterRange := bonus_range 160 (HazardPattern.afterPattern 10000 p (.push 160 (.stay 138)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 160 (.stay 138))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 138))) ∧ bonus (HazardPattern.nextHero (.push 160 (.stay 138))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 138))) ≤ 2 at afterRange
  rw [gammaAfter749] at afterRange
  have possibilities : (d17560 p = 1 ∧ d214541 p = 0) ∨ (d17560 p = 2 ∧ d214541 p = 0) ∨ (d17560 p = 2 ∧ d214541 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro21048 p pair.2
    have combined := andIntro53950 p beforeEq guard
    have complete := andIntro53951 p combined afterEq
    have bound := compare28866 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro21048 p pair.2
    have combined := andIntro53990 p guard beforeEq
    have complete := andIntro53951 p combined afterEq
    have bound := compare28867 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro21193 p pair.2
    have combined := andIntro53990 p guard beforeEq
    have complete := andIntro53991 p combined afterEq
    have bound := compare28866 p complete
    omega
theorem local749 (p : Pattern) (guard : d128487 p = 1)
    (decreasing : bonus 160 (HazardPattern.afterPattern 10000 p (.push 160 (.stay 138))) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 160 (.stay 138)) + NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 160 (.stay 138)))) + bonus 160 (HazardPattern.afterPattern 10000 p (.push 160 (.stay 138))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 160 (.stay 138)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 160 (.stay 138))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 138))) < bonus 182 p at decreasing
  rw [gammaAfter749, at182] at decreasing
  have numeric := numeric749 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 160 (.stay 138))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 138)))
  rw [oldBefore182, at182, literal, oldAfter749, gammaAfter749]
  exact numeric
theorem numeric750 (p : Pattern) (guard : d211415 p = 1) (decreasing : d28738 p < d17560 p) :
    d49280 p + d17560 p ≤ (0 : Int) + d49782 p + d28738 p := by
  have beforeRange := bonus_range 182 p
  rw [at182] at beforeRange
  have afterRange := bonus_range 204 (HazardPattern.afterPattern 10000 p (.walk 204))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) ∧ bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) ≤ 2 at afterRange
  rw [gammaAfter750] at afterRange
  have possibilities : (d17560 p = 1 ∧ d28738 p = 0) ∨ (d17560 p = 2 ∧ d28738 p = 0) ∨ (d17560 p = 2 ∧ d28738 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro20553 p pair.2
    have combined := andIntro53996 p beforeEq guard
    have complete := andIntro53246 p afterEq combined
    have bound := compare28868 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro20553 p pair.2
    have combined := andIntro54001 p beforeEq guard
    have complete := andIntro53290 p afterEq combined
    have bound := compare28869 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro20627 p pair.2
    have combined := andIntro54001 p beforeEq guard
    have complete := andIntro53310 p afterEq combined
    have bound := compare28868 p complete
    omega
theorem local750 (p : Pattern) (guard : d211415 p = 1)
    (decreasing : bonus 204 (HazardPattern.afterPattern 10000 p (.walk 204)) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 204) + NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 204))) + bonus 204 (HazardPattern.afterPattern 10000 p (.walk 204)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 204) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) < bonus 182 p at decreasing
  rw [gammaAfter750, at182] at decreasing
  have numeric := numeric750 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204))
  rw [oldBefore182, at182, literal, oldAfter750, gammaAfter750]
  exact numeric
theorem numeric751 (p : Pattern) (guard : d216471 p = 1) (decreasing : d219218 p < d17560 p) :
    d49280 p + d17560 p ≤ (0 : Int) + d216729 p + d219218 p := by
  have beforeRange := bonus_range 182 p
  rw [at182] at beforeRange
  have afterRange := bonus_range 204 (HazardPattern.afterPattern 10000 p (.push 204 (.stay 226)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 204 (.stay 226))) (HazardPattern.afterPattern 10000 p (.push 204 (.stay 226))) ∧ bonus (HazardPattern.nextHero (.push 204 (.stay 226))) (HazardPattern.afterPattern 10000 p (.push 204 (.stay 226))) ≤ 2 at afterRange
  rw [gammaAfter751] at afterRange
  have possibilities : (d17560 p = 1 ∧ d219218 p = 0) ∨ (d17560 p = 2 ∧ d219218 p = 0) ∨ (d17560 p = 2 ∧ d219218 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro21646 p pair.2
    have combined := andIntro54373 p beforeEq guard
    have complete := andIntro54521 p afterEq combined
    have bound := compare28870 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro21646 p pair.2
    have combined := andIntro54560 p beforeEq guard
    have complete := andIntro54584 p afterEq combined
    have bound := compare28871 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro21815 p pair.2
    have combined := andIntro54560 p beforeEq guard
    have complete := andIntro54604 p combined afterEq
    have bound := compare28870 p complete
    omega
theorem local751 (p : Pattern) (guard : d216471 p = 1)
    (decreasing : bonus 204 (HazardPattern.afterPattern 10000 p (.push 204 (.stay 226))) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 204 (.stay 226)) + NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 204 (.stay 226)))) + bonus 204 (HazardPattern.afterPattern 10000 p (.push 204 (.stay 226))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 204 (.stay 226)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 204 (.stay 226))) (HazardPattern.afterPattern 10000 p (.push 204 (.stay 226))) < bonus 182 p at decreasing
  rw [gammaAfter751, at182] at decreasing
  have numeric := numeric751 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 204 (.stay 226))) (HazardPattern.afterPattern 10000 p (.push 204 (.stay 226)))
  rw [oldBefore182, at182, literal, oldAfter751, gammaAfter751]
  exact numeric
theorem numeric752 (p : Pattern) (guard : d211412 p = 1) (decreasing : d17560 p < d17560 p) :
    d49280 p + d17560 p ≤ (0 : Int) + d47866 p + d17560 p := by
  have beforeRange := bonus_range 182 p
  rw [at182] at beforeRange
  have afterRange := bonus_range 181 (HazardPattern.afterPattern 10000 p (.walk 181))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ∧ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ≤ 2 at afterRange
  rw [gammaAfter752] at afterRange
  have possibilities : (d17560 p = 1 ∧ d17560 p = 0) ∨ (d17560 p = 2 ∧ d17560 p = 0) ∨ (d17560 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro51556 p beforeEq guard
    have complete := andIntro38077 p afterEq combined
    have bound := compare28872 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro51557 p beforeEq guard
    have complete := andIntro38128 p afterEq combined
    have bound := compare28873 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro51557 p beforeEq guard
    have complete := andIntro38172 p afterEq combined
    have bound := compare28872 p complete
    omega
theorem local752 (p : Pattern) (guard : d211412 p = 1)
    (decreasing : bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 181) + NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 181))) + bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 181) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 182 p at decreasing
  rw [gammaAfter752, at182] at decreasing
  have numeric := numeric752 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181))
  rw [oldBefore182, at182, literal, oldAfter752, gammaAfter752]
  exact numeric
theorem numeric753 (p : Pattern) (guard : d207966 p = 1) (decreasing : d223957 p < d17560 p) :
    d49280 p + d17560 p ≤ (2 : Int) + d47866 p + d223957 p := by
  have beforeRange := bonus_range 182 p
  rw [at182] at beforeRange
  have afterRange := bonus_range 181 (HazardPattern.afterPattern 10000 p (.push 181 (.stay 180)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 181 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 181 (.stay 180))) ∧ bonus (HazardPattern.nextHero (.push 181 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 181 (.stay 180))) ≤ 2 at afterRange
  rw [gammaAfter753] at afterRange
  have possibilities : (d17560 p = 1 ∧ d223957 p = 0) ∨ (d17560 p = 2 ∧ d223957 p = 0) ∨ (d17560 p = 2 ∧ d223957 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro22167 p pair.2
    have combined := andIntro54609 p beforeEq guard
    have complete := andIntro54610 p combined afterEq
    have bound := compare28874 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro22167 p pair.2
    have combined := andIntro54615 p beforeEq guard
    have complete := andIntro54610 p combined afterEq
    have bound := compare28875 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro22294 p pair.2
    have combined := andIntro54615 p beforeEq guard
    have complete := andIntro54616 p combined afterEq
    have bound := compare28874 p complete
    omega
theorem local753 (p : Pattern) (guard : d207966 p = 1)
    (decreasing : bonus 181 (HazardPattern.afterPattern 10000 p (.push 181 (.stay 180))) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 181 (.stay 180)) + NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 181 (.stay 180)))) + bonus 181 (HazardPattern.afterPattern 10000 p (.push 181 (.stay 180))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 181 (.stay 180)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 181 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 181 (.stay 180))) < bonus 182 p at decreasing
  rw [gammaAfter753, at182] at decreasing
  have numeric := numeric753 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 181 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 181 (.stay 180)))
  rw [oldBefore182, at182, literal, oldAfter753, gammaAfter753]
  exact numeric
theorem numeric754 (p : Pattern) (guard : d187678 p = 1) (decreasing : d18533 p < d17560 p) :
    d49280 p + d17560 p ≤ (0 : Int) + d48547 p + d18533 p := by
  have beforeRange := bonus_range 182 p
  rw [at182] at beforeRange
  have afterRange := bonus_range 161 (HazardPattern.afterPattern 10000 p (.walk 161))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) ∧ bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) ≤ 2 at afterRange
  rw [gammaAfter754] at afterRange
  have possibilities : (d17560 p = 1 ∧ d18533 p = 0) ∨ (d17560 p = 2 ∧ d18533 p = 0) ∨ (d17560 p = 2 ∧ d18533 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro10408 p pair.2
    have combined := andIntro54941 p beforeEq guard
    have complete := andIntro39022 p afterEq combined
    have bound := compare28876 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10408 p pair.2
    have combined := andIntro54980 p beforeEq guard
    have complete := andIntro39095 p afterEq combined
    have bound := compare28877 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro10478 p pair.2
    have combined := andIntro54980 p beforeEq guard
    have complete := andIntro39123 p afterEq combined
    have bound := compare28876 p complete
    omega
theorem local754 (p : Pattern) (guard : d187678 p = 1)
    (decreasing : bonus 161 (HazardPattern.afterPattern 10000 p (.walk 161)) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 161) + NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 161))) + bonus 161 (HazardPattern.afterPattern 10000 p (.walk 161)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 161) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) < bonus 182 p at decreasing
  rw [gammaAfter754, at182] at decreasing
  have numeric := numeric754 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161))
  rw [oldBefore182, at182, literal, oldAfter754, gammaAfter754]
  exact numeric
theorem numeric755 (p : Pattern) (guard : d169391 p = 1) (decreasing : d15965 p < d17560 p) :
    d49280 p + d17560 p ≤ (0 : Int) + d47866 p + d15965 p := by
  have beforeRange := bonus_range 182 p
  rw [at182] at beforeRange
  have afterRange := bonus_range 159 (HazardPattern.afterPattern 10000 p (.walk 159))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ∧ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ≤ 2 at afterRange
  rw [gammaAfter755] at afterRange
  have possibilities : (d17560 p = 1 ∧ d15965 p = 0) ∨ (d17560 p = 2 ∧ d15965 p = 0) ∨ (d17560 p = 2 ∧ d15965 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10254 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro55264 p beforeEq guard
    have complete := andIntro40006 p afterEq combined
    have bound := compare28872 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro55302 p guard beforeEq
    have complete := andIntro40094 p afterEq combined
    have bound := compare28873 p complete
    omega
  · have beforeEq := eqIntro15530 p pair.1
    have afterEq := eqIntro9862 p pair.2
    have combined := andIntro55302 p guard beforeEq
    have complete := andIntro40138 p afterEq combined
    have bound := compare28872 p complete
    omega
theorem local755 (p : Pattern) (guard : d169391 p = 1)
    (decreasing : bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 159) + NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 159))) + bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 159) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 182 p at decreasing
  rw [gammaAfter755, at182] at decreasing
  have numeric := numeric755 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159))
  rw [oldBefore182, at182, literal, oldAfter755, gammaAfter755]
  exact numeric
theorem numeric756 (p : Pattern) (guard : d187679 p = 1) (decreasing : d19737 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d48749 p + d19737 p := by
  have beforeRange := bonus_range 184 p
  rw [at184] at beforeRange
  have afterRange := bonus_range 162 (HazardPattern.afterPattern 10000 p (.walk 162))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) ∧ bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) ≤ 2 at afterRange
  rw [gammaAfter756] at afterRange
  have possibilities : (d20891 p = 1 ∧ d19737 p = 0) ∨ (d20891 p = 2 ∧ d19737 p = 0) ∨ (d20891 p = 2 ∧ d19737 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro11154 p pair.2
    have combined := andIntro55445 p beforeEq guard
    have complete := andIntro55557 p afterEq combined
    have bound := compare28878 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro11154 p pair.2
    have combined := andIntro55590 p guard beforeEq
    have complete := andIntro55624 p afterEq combined
    have bound := compare28879 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro11224 p pair.2
    have combined := andIntro55590 p guard beforeEq
    have complete := andIntro55652 p afterEq combined
    have bound := compare28878 p complete
    omega
theorem local756 (p : Pattern) (guard : d187679 p = 1)
    (decreasing : bonus 162 (HazardPattern.afterPattern 10000 p (.walk 162)) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 162) + NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 162))) + bonus 162 (HazardPattern.afterPattern 10000 p (.walk 162)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 162) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) < bonus 184 p at decreasing
  rw [gammaAfter756, at184] at decreasing
  have numeric := numeric756 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162))
  rw [oldBefore184, at184, literal, oldAfter756, gammaAfter756]
  exact numeric
theorem numeric757 (p : Pattern) (guard : d225586 p = 1) (decreasing : d20891 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 184 p
  rw [at184] at beforeRange
  have afterRange := bonus_range 185 (HazardPattern.afterPattern 10000 p (.walk 185))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) ∧ bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) ≤ 2 at afterRange
  rw [gammaAfter757] at afterRange
  have possibilities : (d20891 p = 1 ∧ d20891 p = 0) ∨ (d20891 p = 2 ∧ d20891 p = 0) ∨ (d20891 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro55653 p beforeEq guard
    have complete := andIntro44902 p afterEq combined
    have bound := compare28850 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro55654 p beforeEq guard
    have complete := andIntro44937 p afterEq combined
    have bound := compare28851 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro55654 p beforeEq guard
    have complete := andIntro44965 p afterEq combined
    have bound := compare28850 p complete
    omega
theorem local757 (p : Pattern) (guard : d225586 p = 1)
    (decreasing : bonus 185 (HazardPattern.afterPattern 10000 p (.walk 185)) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 185) + NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 185))) + bonus 185 (HazardPattern.afterPattern 10000 p (.walk 185)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 185) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) < bonus 184 p at decreasing
  rw [gammaAfter757, at184] at decreasing
  have numeric := numeric757 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185))
  rw [oldBefore184, at184, literal, oldAfter757, gammaAfter757]
  exact numeric
theorem numeric758 (p : Pattern) (guard : d225589 p = 1) (decreasing : d0 p < d20891 p) :
    d49102 p + d20891 p ≤ (1 : Int) + d49102 p + d0 p := by
  have beforeRange := bonus_range 184 p
  rw [at184] at beforeRange
  have afterRange := bonus_range 185 (HazardPattern.afterPattern 10000 p (.push 185 (.stay 186)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 185 (.stay 186))) (HazardPattern.afterPattern 10000 p (.push 185 (.stay 186))) ∧ bonus (HazardPattern.nextHero (.push 185 (.stay 186))) (HazardPattern.afterPattern 10000 p (.push 185 (.stay 186))) ≤ 2 at afterRange
  rw [gammaAfter758] at afterRange
  have possibilities : (d20891 p = 1 ∧ d0 p = 0) ∨ (d20891 p = 2 ∧ d0 p = 0) ∨ (d20891 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro55659 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare28880 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro55664 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare28850 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro55664 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare28880 p complete
    omega
theorem local758 (p : Pattern) (guard : d225589 p = 1)
    (decreasing : bonus 185 (HazardPattern.afterPattern 10000 p (.push 185 (.stay 186))) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 185 (.stay 186)) + NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 185 (.stay 186)))) + bonus 185 (HazardPattern.afterPattern 10000 p (.push 185 (.stay 186))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 185 (.stay 186)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 185 (.stay 186))) (HazardPattern.afterPattern 10000 p (.push 185 (.stay 186))) < bonus 184 p at decreasing
  rw [gammaAfter758, at184] at decreasing
  have numeric := numeric758 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 185 (.stay 186))) (HazardPattern.afterPattern 10000 p (.push 185 (.stay 186)))
  rw [oldBefore184, at184, literal, oldAfter758, gammaAfter758]
  exact numeric
theorem numeric759 (p : Pattern) (guard : d192716 p = 1) (decreasing : d20389 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d48997 p + d20389 p := by
  have beforeRange := bonus_range 184 p
  rw [at184] at beforeRange
  have afterRange := bonus_range 163 (HazardPattern.afterPattern 10000 p (.walk 163))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) ∧ bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) ≤ 2 at afterRange
  rw [gammaAfter759] at afterRange
  have possibilities : (d20891 p = 1 ∧ d20389 p = 0) ∨ (d20891 p = 2 ∧ d20389 p = 0) ∨ (d20891 p = 2 ∧ d20389 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro10791 p pair.2
    have combined := andIntro55669 p beforeEq guard
    have complete := andIntro45158 p afterEq combined
    have bound := compare28852 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10791 p pair.2
    have combined := andIntro55674 p guard beforeEq
    have complete := andIntro45225 p afterEq combined
    have bound := compare28853 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10843 p pair.2
    have combined := andIntro55674 p guard beforeEq
    have complete := andIntro45253 p afterEq combined
    have bound := compare28852 p complete
    omega
theorem local759 (p : Pattern) (guard : d192716 p = 1)
    (decreasing : bonus 163 (HazardPattern.afterPattern 10000 p (.walk 163)) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 163) + NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 163))) + bonus 163 (HazardPattern.afterPattern 10000 p (.walk 163)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 163) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) < bonus 184 p at decreasing
  rw [gammaAfter759, at184] at decreasing
  have numeric := numeric759 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163))
  rw [oldBefore184, at184, literal, oldAfter759, gammaAfter759]
  exact numeric
theorem numeric760 (p : Pattern) (guard : d187676 p = 1) (decreasing : d18533 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d48547 p + d18533 p := by
  have beforeRange := bonus_range 184 p
  rw [at184] at beforeRange
  have afterRange := bonus_range 161 (HazardPattern.afterPattern 10000 p (.walk 161))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) ∧ bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) ≤ 2 at afterRange
  rw [gammaAfter760] at afterRange
  have possibilities : (d20891 p = 1 ∧ d18533 p = 0) ∨ (d20891 p = 2 ∧ d18533 p = 0) ∨ (d20891 p = 2 ∧ d18533 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro10408 p pair.2
    have combined := andIntro55817 p beforeEq guard
    have complete := andIntro43015 p afterEq combined
    have bound := compare28881 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10408 p pair.2
    have combined := andIntro55850 p guard beforeEq
    have complete := andIntro43082 p afterEq combined
    have bound := compare28882 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10478 p pair.2
    have combined := andIntro55850 p guard beforeEq
    have complete := andIntro43110 p afterEq combined
    have bound := compare28881 p complete
    omega
theorem local760 (p : Pattern) (guard : d187676 p = 1)
    (decreasing : bonus 161 (HazardPattern.afterPattern 10000 p (.walk 161)) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 161) + NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 161))) + bonus 161 (HazardPattern.afterPattern 10000 p (.walk 161)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 161) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) < bonus 184 p at decreasing
  rw [gammaAfter760, at184] at decreasing
  have numeric := numeric760 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161))
  rw [oldBefore184, at184, literal, oldAfter760, gammaAfter760]
  exact numeric
theorem numeric761 (p : Pattern) (guard : d190593 p = 1) (decreasing : d20389 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d48997 p + d20389 p := by
  have beforeRange := bonus_range 185 p
  rw [at185] at beforeRange
  have afterRange := bonus_range 163 (HazardPattern.afterPattern 10000 p (.walk 163))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) ∧ bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) ≤ 2 at afterRange
  rw [gammaAfter761] at afterRange
  have possibilities : (d20891 p = 1 ∧ d20389 p = 0) ∨ (d20891 p = 2 ∧ d20389 p = 0) ∨ (d20891 p = 2 ∧ d20389 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro10791 p pair.2
    have combined := andIntro55855 p beforeEq guard
    have complete := andIntro45158 p afterEq combined
    have bound := compare28852 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10791 p pair.2
    have combined := andIntro55860 p guard beforeEq
    have complete := andIntro45225 p afterEq combined
    have bound := compare28853 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10843 p pair.2
    have combined := andIntro55860 p guard beforeEq
    have complete := andIntro45253 p afterEq combined
    have bound := compare28852 p complete
    omega
theorem local761 (p : Pattern) (guard : d190593 p = 1)
    (decreasing : bonus 163 (HazardPattern.afterPattern 10000 p (.walk 163)) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 163) + NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 163))) + bonus 163 (HazardPattern.afterPattern 10000 p (.walk 163)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 163) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) < bonus 185 p at decreasing
  rw [gammaAfter761, at185] at decreasing
  have numeric := numeric761 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163))
  rw [oldBefore185, at185, literal, oldAfter761, gammaAfter761]
  exact numeric
theorem numeric762 (p : Pattern) (guard : d130390 p = 1) (decreasing : d226708 p < d20891 p) :
    d49102 p + d20891 p ≤ (2 : Int) + d225614 p + d226708 p := by
  have beforeRange := bonus_range 185 p
  rw [at185] at beforeRange
  have afterRange := bonus_range 163 (HazardPattern.afterPattern 10000 p (.push 163 (.stay 141)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 163 (.stay 141))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 141))) ∧ bonus (HazardPattern.nextHero (.push 163 (.stay 141))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 141))) ≤ 2 at afterRange
  rw [gammaAfter762] at afterRange
  have possibilities : (d20891 p = 1 ∧ d226708 p = 0) ∨ (d20891 p = 2 ∧ d226708 p = 0) ∨ (d20891 p = 2 ∧ d226708 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro22448 p pair.2
    have combined := andIntro55941 p guard beforeEq
    have complete := andIntro55942 p combined afterEq
    have bound := compare28883 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro22448 p pair.2
    have combined := andIntro55975 p guard beforeEq
    have complete := andIntro55942 p combined afterEq
    have bound := compare28884 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro22518 p pair.2
    have combined := andIntro55975 p guard beforeEq
    have complete := andIntro55976 p combined afterEq
    have bound := compare28883 p complete
    omega
theorem local762 (p : Pattern) (guard : d130390 p = 1)
    (decreasing : bonus 163 (HazardPattern.afterPattern 10000 p (.push 163 (.stay 141))) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 163 (.stay 141)) + NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 163 (.stay 141)))) + bonus 163 (HazardPattern.afterPattern 10000 p (.push 163 (.stay 141))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 163 (.stay 141)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 163 (.stay 141))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 141))) < bonus 185 p at decreasing
  rw [gammaAfter762, at185] at decreasing
  have numeric := numeric762 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 163 (.stay 141))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 141)))
  rw [oldBefore185, at185, literal, oldAfter762, gammaAfter762]
  exact numeric
theorem numeric763 (p : Pattern) (guard : d227682 p = 1) (decreasing : d20891 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 185 p
  rw [at185] at beforeRange
  have afterRange := bonus_range 186 (HazardPattern.afterPattern 10000 p (.walk 186))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186)) ∧ bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186)) ≤ 2 at afterRange
  rw [gammaAfter763] at afterRange
  have possibilities : (d20891 p = 1 ∧ d20891 p = 0) ∨ (d20891 p = 2 ∧ d20891 p = 0) ∨ (d20891 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro55977 p beforeEq guard
    have complete := andIntro44902 p afterEq combined
    have bound := compare28850 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro55978 p beforeEq guard
    have complete := andIntro44937 p afterEq combined
    have bound := compare28851 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro55978 p beforeEq guard
    have complete := andIntro44965 p afterEq combined
    have bound := compare28850 p complete
    omega
theorem local763 (p : Pattern) (guard : d227682 p = 1)
    (decreasing : bonus 186 (HazardPattern.afterPattern 10000 p (.walk 186)) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 186) + NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 186))) + bonus 186 (HazardPattern.afterPattern 10000 p (.walk 186)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 186) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186)) < bonus 185 p at decreasing
  rw [gammaAfter763, at185] at decreasing
  have numeric := numeric763 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186))
  rw [oldBefore185, at185, literal, oldAfter763, gammaAfter763]
  exact numeric
theorem numeric764 (p : Pattern) (guard : d225586 p = 1) (decreasing : d20891 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 185 p
  rw [at185] at beforeRange
  have afterRange := bonus_range 184 (HazardPattern.afterPattern 10000 p (.walk 184))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) ∧ bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) ≤ 2 at afterRange
  rw [gammaAfter764] at afterRange
  have possibilities : (d20891 p = 1 ∧ d20891 p = 0) ∨ (d20891 p = 2 ∧ d20891 p = 0) ∨ (d20891 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro55653 p beforeEq guard
    have complete := andIntro44902 p afterEq combined
    have bound := compare28850 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro55654 p beforeEq guard
    have complete := andIntro44937 p afterEq combined
    have bound := compare28851 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro55654 p beforeEq guard
    have complete := andIntro44965 p afterEq combined
    have bound := compare28850 p complete
    omega
theorem local764 (p : Pattern) (guard : d225586 p = 1)
    (decreasing : bonus 184 (HazardPattern.afterPattern 10000 p (.walk 184)) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 184) + NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 184))) + bonus 184 (HazardPattern.afterPattern 10000 p (.walk 184)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 184) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) < bonus 185 p at decreasing
  rw [gammaAfter764, at185] at decreasing
  have numeric := numeric764 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184))
  rw [oldBefore185, at185, literal, oldAfter764, gammaAfter764]
  exact numeric
theorem numeric765 (p : Pattern) (guard : d194332 p = 1) (decreasing : d20891 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 185 p
  rw [at185] at beforeRange
  have afterRange := bonus_range 164 (HazardPattern.afterPattern 10000 p (.walk 164))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) ∧ bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) ≤ 2 at afterRange
  rw [gammaAfter765] at afterRange
  have possibilities : (d20891 p = 1 ∧ d20891 p = 0) ∨ (d20891 p = 2 ∧ d20891 p = 0) ∨ (d20891 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro45718 p beforeEq guard
    have complete := andIntro44902 p afterEq combined
    have bound := compare28850 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro45719 p beforeEq guard
    have complete := andIntro44937 p afterEq combined
    have bound := compare28851 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro45719 p beforeEq guard
    have complete := andIntro44965 p afterEq combined
    have bound := compare28850 p complete
    omega
theorem local765 (p : Pattern) (guard : d194332 p = 1)
    (decreasing : bonus 164 (HazardPattern.afterPattern 10000 p (.walk 164)) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 164) + NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 164))) + bonus 164 (HazardPattern.afterPattern 10000 p (.walk 164)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 164) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) < bonus 185 p at decreasing
  rw [gammaAfter765, at185] at decreasing
  have numeric := numeric765 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164))
  rw [oldBefore185, at185, literal, oldAfter765, gammaAfter765]
  exact numeric
theorem numeric766 (p : Pattern) (guard : d188524 p = 1) (decreasing : d19737 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d48749 p + d19737 p := by
  have beforeRange := bonus_range 185 p
  rw [at185] at beforeRange
  have afterRange := bonus_range 162 (HazardPattern.afterPattern 10000 p (.walk 162))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) ∧ bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) ≤ 2 at afterRange
  rw [gammaAfter766] at afterRange
  have possibilities : (d20891 p = 1 ∧ d19737 p = 0) ∨ (d20891 p = 2 ∧ d19737 p = 0) ∨ (d20891 p = 2 ∧ d19737 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro11154 p pair.2
    have combined := andIntro55983 p beforeEq guard
    have complete := andIntro55557 p afterEq combined
    have bound := compare28878 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro11154 p pair.2
    have combined := andIntro55988 p guard beforeEq
    have complete := andIntro55624 p afterEq combined
    have bound := compare28879 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro11224 p pair.2
    have combined := andIntro55988 p guard beforeEq
    have complete := andIntro55652 p afterEq combined
    have bound := compare28878 p complete
    omega
theorem local766 (p : Pattern) (guard : d188524 p = 1)
    (decreasing : bonus 162 (HazardPattern.afterPattern 10000 p (.walk 162)) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 162) + NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 162))) + bonus 162 (HazardPattern.afterPattern 10000 p (.walk 162)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 162) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) < bonus 185 p at decreasing
  rw [gammaAfter766, at185] at decreasing
  have numeric := numeric766 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162))
  rw [oldBefore185, at185, literal, oldAfter766, gammaAfter766]
  exact numeric
theorem numeric767 (p : Pattern) (guard : d192717 p = 1) (decreasing : d20891 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 186 p
  rw [at186] at beforeRange
  have afterRange := bonus_range 164 (HazardPattern.afterPattern 10000 p (.walk 164))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) ∧ bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) ≤ 2 at afterRange
  rw [gammaAfter767] at afterRange
  have possibilities : (d20891 p = 1 ∧ d20891 p = 0) ∨ (d20891 p = 2 ∧ d20891 p = 0) ∨ (d20891 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro44821 p beforeEq guard
    have complete := andIntro44902 p afterEq combined
    have bound := compare28850 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro44903 p guard beforeEq
    have complete := andIntro44937 p afterEq combined
    have bound := compare28851 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro44903 p guard beforeEq
    have complete := andIntro44965 p afterEq combined
    have bound := compare28850 p complete
    omega
theorem local767 (p : Pattern) (guard : d192717 p = 1)
    (decreasing : bonus 164 (HazardPattern.afterPattern 10000 p (.walk 164)) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 164) + NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 164))) + bonus 164 (HazardPattern.afterPattern 10000 p (.walk 164)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 164) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) < bonus 186 p at decreasing
  rw [gammaAfter767, at186] at decreasing
  have numeric := numeric767 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164))
  rw [oldBefore186, at186, literal, oldAfter767, gammaAfter767]
  exact numeric
theorem numeric768 (p : Pattern) (guard : d227682 p = 1) (decreasing : d20891 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 186 p
  rw [at186] at beforeRange
  have afterRange := bonus_range 185 (HazardPattern.afterPattern 10000 p (.walk 185))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) ∧ bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) ≤ 2 at afterRange
  rw [gammaAfter768] at afterRange
  have possibilities : (d20891 p = 1 ∧ d20891 p = 0) ∨ (d20891 p = 2 ∧ d20891 p = 0) ∨ (d20891 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro55977 p beforeEq guard
    have complete := andIntro44902 p afterEq combined
    have bound := compare28850 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro55978 p beforeEq guard
    have complete := andIntro44937 p afterEq combined
    have bound := compare28851 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro55978 p beforeEq guard
    have complete := andIntro44965 p afterEq combined
    have bound := compare28850 p complete
    omega
theorem local768 (p : Pattern) (guard : d227682 p = 1)
    (decreasing : bonus 185 (HazardPattern.afterPattern 10000 p (.walk 185)) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 185) + NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 185))) + bonus 185 (HazardPattern.afterPattern 10000 p (.walk 185)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 185) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) < bonus 186 p at decreasing
  rw [gammaAfter768, at186] at decreasing
  have numeric := numeric768 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185))
  rw [oldBefore186, at186, literal, oldAfter768, gammaAfter768]
  exact numeric
theorem numeric769 (p : Pattern) (guard : d225589 p = 1) (decreasing : d0 p < d20891 p) :
    d49102 p + d20891 p ≤ (1 : Int) + d49102 p + d0 p := by
  have beforeRange := bonus_range 186 p
  rw [at186] at beforeRange
  have afterRange := bonus_range 185 (HazardPattern.afterPattern 10000 p (.push 185 (.stay 184)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 185 (.stay 184))) (HazardPattern.afterPattern 10000 p (.push 185 (.stay 184))) ∧ bonus (HazardPattern.nextHero (.push 185 (.stay 184))) (HazardPattern.afterPattern 10000 p (.push 185 (.stay 184))) ≤ 2 at afterRange
  rw [gammaAfter769] at afterRange
  have possibilities : (d20891 p = 1 ∧ d0 p = 0) ∨ (d20891 p = 2 ∧ d0 p = 0) ∨ (d20891 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro55659 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare28880 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro55664 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare28850 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro55664 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare28880 p complete
    omega
theorem local769 (p : Pattern) (guard : d225589 p = 1)
    (decreasing : bonus 185 (HazardPattern.afterPattern 10000 p (.push 185 (.stay 184))) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 185 (.stay 184)) + NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 185 (.stay 184)))) + bonus 185 (HazardPattern.afterPattern 10000 p (.push 185 (.stay 184))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 185 (.stay 184)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 185 (.stay 184))) (HazardPattern.afterPattern 10000 p (.push 185 (.stay 184))) < bonus 186 p at decreasing
  rw [gammaAfter769, at186] at decreasing
  have numeric := numeric769 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 185 (.stay 184))) (HazardPattern.afterPattern 10000 p (.push 185 (.stay 184)))
  rw [oldBefore186, at186, literal, oldAfter769, gammaAfter769]
  exact numeric
end NetHack.Soko22Hazard87
