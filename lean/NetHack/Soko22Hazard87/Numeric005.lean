import NetHack.Soko22Hazard87.Numeric004
import NetHack.Soko22Hazard87.AndIntroBlocks0057
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric350 (p : Pattern) (guard : d100900 p = 1) (decreasing : d0 p < d0 p) :
    d48097 p + d0 p ≤ (0 : Int) + d48251 p + d0 p := by
  have beforeRange := bonus_range 115 p
  rw [at115] at beforeRange
  have afterRange := bonus_range 138 (HazardPattern.afterPattern 10000 p (.walk 138))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) ∧ bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) ≤ 2 at afterRange
  rw [gammaAfter350] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14399 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10050 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14399 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10051 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14399 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10050 p complete
    omega
theorem local350 (p : Pattern) (guard : d100900 p = 1)
    (decreasing : bonus 138 (HazardPattern.afterPattern 10000 p (.walk 138)) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 138) + NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 138))) + bonus 138 (HazardPattern.afterPattern 10000 p (.walk 138)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 138) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) < bonus 115 p at decreasing
  rw [gammaAfter350, at115] at decreasing
  have numeric := numeric350 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138))
  rw [oldBefore115, at115, literal, oldAfter350, gammaAfter350]
  exact numeric
theorem numeric351 (p : Pattern) (guard : d100902 p = 1) (decreasing : d9291 p < d0 p) :
    d48097 p + d0 p ≤ (0 : Int) + d47866 p + d9291 p := by
  have beforeRange := bonus_range 115 p
  rw [at115] at beforeRange
  have afterRange := bonus_range 136 (HazardPattern.afterPattern 10000 p (.walk 136))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ∧ bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) ≤ 2 at afterRange
  rw [gammaAfter351] at afterRange
  have possibilities : (d0 p = 1 ∧ d9291 p = 0) ∨ (d0 p = 2 ∧ d9291 p = 0) ∨ (d0 p = 2 ∧ d9291 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro14400 p beforeEq guard
    have complete := andIntro14401 p combined afterEq
    have bound := compare10046 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro5827 p pair.2
    have combined := andIntro14400 p beforeEq guard
    have complete := andIntro14401 p combined afterEq
    have bound := compare10047 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro5906 p pair.2
    have combined := andIntro14400 p beforeEq guard
    have complete := andIntro14402 p combined afterEq
    have bound := compare10046 p complete
    omega
theorem local351 (p : Pattern) (guard : d100902 p = 1)
    (decreasing : bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 136) + NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 136))) + bonus 136 (HazardPattern.afterPattern 10000 p (.walk 136)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 136) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) < bonus 115 p at decreasing
  rw [gammaAfter351, at115] at decreasing
  have numeric := numeric351 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136))
  rw [oldBefore115, at115, literal, oldAfter351, gammaAfter351]
  exact numeric
theorem numeric352 (p : Pattern) (guard : d82335 p = 1) (decreasing : d0 p < d0 p) :
    d48115 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 116 p
  rw [at116] at beforeRange
  have afterRange := bonus_range 94 (HazardPattern.afterPattern 10000 p (.walk 94))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) ∧ bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) ≤ 2 at afterRange
  rw [gammaAfter352] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9134 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10052 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9134 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10053 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9134 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10052 p complete
    omega
theorem local352 (p : Pattern) (guard : d82335 p = 1)
    (decreasing : bonus 94 (HazardPattern.afterPattern 10000 p (.walk 94)) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 94) + NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 94))) + bonus 94 (HazardPattern.afterPattern 10000 p (.walk 94)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 94) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) < bonus 116 p at decreasing
  rw [gammaAfter352, at116] at decreasing
  have numeric := numeric352 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94))
  rw [oldBefore116, at116, literal, oldAfter352, gammaAfter352]
  exact numeric
theorem numeric353 (p : Pattern) (guard : d100899 p = 1) (decreasing : d0 p < d0 p) :
    d48115 p + d0 p ≤ (0 : Int) + d48251 p + d0 p := by
  have beforeRange := bonus_range 116 p
  rw [at116] at beforeRange
  have afterRange := bonus_range 138 (HazardPattern.afterPattern 10000 p (.walk 138))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) ∧ bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) ≤ 2 at afterRange
  rw [gammaAfter353] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14403 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10054 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14403 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10055 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14403 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10054 p complete
    omega
theorem local353 (p : Pattern) (guard : d100899 p = 1)
    (decreasing : bonus 138 (HazardPattern.afterPattern 10000 p (.walk 138)) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 138) + NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 138))) + bonus 138 (HazardPattern.afterPattern 10000 p (.walk 138)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 138) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) < bonus 116 p at decreasing
  rw [gammaAfter353, at116] at decreasing
  have numeric := numeric353 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138))
  rw [oldBefore116, at116, literal, oldAfter353, gammaAfter353]
  exact numeric
theorem numeric354 (p : Pattern) (guard : d100907 p = 1) (decreasing : d0 p < d0 p) :
    d48115 p + d0 p ≤ (0 : Int) + d100929 p + d0 p := by
  have beforeRange := bonus_range 116 p
  rw [at116] at beforeRange
  have afterRange := bonus_range 138 (HazardPattern.afterPattern 10000 p (.push 138 (.stay 160)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 138 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 138 (.stay 160))) ∧ bonus (HazardPattern.nextHero (.push 138 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 138 (.stay 160))) ≤ 2 at afterRange
  rw [gammaAfter354] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14404 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10056 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14404 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10057 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14404 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10056 p complete
    omega
theorem local354 (p : Pattern) (guard : d100907 p = 1)
    (decreasing : bonus 138 (HazardPattern.afterPattern 10000 p (.push 138 (.stay 160))) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 138 (.stay 160)) + NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 138 (.stay 160)))) + bonus 138 (HazardPattern.afterPattern 10000 p (.push 138 (.stay 160))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 138 (.stay 160)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 138 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 138 (.stay 160))) < bonus 116 p at decreasing
  rw [gammaAfter354, at116] at decreasing
  have numeric := numeric354 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 138 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 138 (.stay 160)))
  rw [oldBefore116, at116, literal, oldAfter354, gammaAfter354]
  exact numeric
theorem numeric355 (p : Pattern) (guard : d82331 p = 1) (decreasing : d0 p < d0 p) :
    d48115 p + d0 p ≤ (0 : Int) + d48097 p + d0 p := by
  have beforeRange := bonus_range 116 p
  rw [at116] at beforeRange
  have afterRange := bonus_range 115 (HazardPattern.afterPattern 10000 p (.walk 115))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) ∧ bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) ≤ 2 at afterRange
  rw [gammaAfter355] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14394 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10058 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14394 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10059 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14394 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10058 p complete
    omega
theorem local355 (p : Pattern) (guard : d82331 p = 1)
    (decreasing : bonus 115 (HazardPattern.afterPattern 10000 p (.walk 115)) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 115) + NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 115))) + bonus 115 (HazardPattern.afterPattern 10000 p (.walk 115)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 115) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) < bonus 116 p at decreasing
  rw [gammaAfter355, at116] at decreasing
  have numeric := numeric355 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115))
  rw [oldBefore116, at116, literal, oldAfter355, gammaAfter355]
  exact numeric
theorem numeric356 (p : Pattern) (guard : d98791 p = 1) (decreasing : d0 p < d0 p) :
    d48115 p + d0 p ≤ (2 : Int) + d100934 p + d0 p := by
  have beforeRange := bonus_range 116 p
  rw [at116] at beforeRange
  have afterRange := bonus_range 115 (HazardPattern.afterPattern 10000 p (.push 115 (.stay 114)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 115 (.stay 114))) (HazardPattern.afterPattern 10000 p (.push 115 (.stay 114))) ∧ bonus (HazardPattern.nextHero (.push 115 (.stay 114))) (HazardPattern.afterPattern 10000 p (.push 115 (.stay 114))) ≤ 2 at afterRange
  rw [gammaAfter356] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14405 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10060 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14405 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10061 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14405 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10060 p complete
    omega
theorem local356 (p : Pattern) (guard : d98791 p = 1)
    (decreasing : bonus 115 (HazardPattern.afterPattern 10000 p (.push 115 (.stay 114))) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 115 (.stay 114)) + NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 115 (.stay 114)))) + bonus 115 (HazardPattern.afterPattern 10000 p (.push 115 (.stay 114))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 115 (.stay 114)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 115 (.stay 114))) (HazardPattern.afterPattern 10000 p (.push 115 (.stay 114))) < bonus 116 p at decreasing
  rw [gammaAfter356, at116] at decreasing
  have numeric := numeric356 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 115 (.stay 114))) (HazardPattern.afterPattern 10000 p (.push 115 (.stay 114)))
  rw [oldBefore116, at116, literal, oldAfter356, gammaAfter356]
  exact numeric
theorem numeric357 (p : Pattern) (guard : d82362 p = 1) (decreasing : d0 p < d0 p) :
    d48115 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 116 p
  rw [at116] at beforeRange
  have afterRange := bonus_range 95 (HazardPattern.afterPattern 10000 p (.walk 95))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) ∧ bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) ≤ 2 at afterRange
  rw [gammaAfter357] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9144 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10052 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9144 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10053 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9144 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10052 p complete
    omega
theorem local357 (p : Pattern) (guard : d82362 p = 1)
    (decreasing : bonus 95 (HazardPattern.afterPattern 10000 p (.walk 95)) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 95) + NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 95))) + bonus 95 (HazardPattern.afterPattern 10000 p (.walk 95)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 95) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) < bonus 116 p at decreasing
  rw [gammaAfter357, at116] at decreasing
  have numeric := numeric357 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95))
  rw [oldBefore116, at116, literal, oldAfter357, gammaAfter357]
  exact numeric
theorem numeric358 (p : Pattern) (guard : d82333 p = 1) (decreasing : d0 p < d0 p) :
    d48115 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 116 p
  rw [at116] at beforeRange
  have afterRange := bonus_range 93 (HazardPattern.afterPattern 10000 p (.walk 93))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) ∧ bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) ≤ 2 at afterRange
  rw [gammaAfter358] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9130 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10052 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9130 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10053 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9130 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10052 p complete
    omega
theorem local358 (p : Pattern) (guard : d82333 p = 1)
    (decreasing : bonus 93 (HazardPattern.afterPattern 10000 p (.walk 93)) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 93) + NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 93))) + bonus 93 (HazardPattern.afterPattern 10000 p (.walk 93)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 93) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) < bonus 116 p at decreasing
  rw [gammaAfter358, at116] at decreasing
  have numeric := numeric358 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93))
  rw [oldBefore116, at116, literal, oldAfter358, gammaAfter358]
  exact numeric
theorem numeric359 (p : Pattern) (guard : d82363 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 118 p
  rw [at118] at beforeRange
  have afterRange := bonus_range 96 (HazardPattern.afterPattern 10000 p (.walk 96))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) ∧ bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) ≤ 2 at afterRange
  rw [gammaAfter359] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9146 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9146 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9146 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local359 (p : Pattern) (guard : d82363 p = 1)
    (decreasing : bonus 96 (HazardPattern.afterPattern 10000 p (.walk 96)) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 96) + NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 96))) + bonus 96 (HazardPattern.afterPattern 10000 p (.walk 96)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 96) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) < bonus 118 p at decreasing
  rw [gammaAfter359, at118] at decreasing
  have numeric := numeric359 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96))
  rw [oldBefore118, at118, literal, oldAfter359, gammaAfter359]
  exact numeric
theorem numeric360 (p : Pattern) (guard : d74052 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 118 p
  rw [at118] at beforeRange
  have afterRange := bonus_range 96 (HazardPattern.afterPattern 10000 p (.push 96 (.stay 74)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 96 (.stay 74))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 74))) ∧ bonus (HazardPattern.nextHero (.push 96 (.stay 74))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 74))) ≤ 2 at afterRange
  rw [gammaAfter360] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6657 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6657 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6657 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local360 (p : Pattern) (guard : d74052 p = 1)
    (decreasing : bonus 96 (HazardPattern.afterPattern 10000 p (.push 96 (.stay 74))) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 96 (.stay 74)) + NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 96 (.stay 74)))) + bonus 96 (HazardPattern.afterPattern 10000 p (.push 96 (.stay 74))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 96 (.stay 74)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 96 (.stay 74))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 74))) < bonus 118 p at decreasing
  rw [gammaAfter360, at118] at decreasing
  have numeric := numeric360 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 96 (.stay 74))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 74)))
  rw [oldBefore118, at118, literal, oldAfter360, gammaAfter360]
  exact numeric
theorem numeric361 (p : Pattern) (guard : d100937 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 118 p
  rw [at118] at beforeRange
  have afterRange := bonus_range 119 (HazardPattern.afterPattern 10000 p (.walk 119))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) ∧ bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) ≤ 2 at afterRange
  rw [gammaAfter361] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14406 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14406 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14406 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local361 (p : Pattern) (guard : d100937 p = 1)
    (decreasing : bonus 119 (HazardPattern.afterPattern 10000 p (.walk 119)) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 119) + NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 119))) + bonus 119 (HazardPattern.afterPattern 10000 p (.walk 119)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 119) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) < bonus 118 p at decreasing
  rw [gammaAfter361, at118] at decreasing
  have numeric := numeric361 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119))
  rw [oldBefore118, at118, literal, oldAfter361, gammaAfter361]
  exact numeric
theorem numeric362 (p : Pattern) (guard : d100940 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (2 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 118 p
  rw [at118] at beforeRange
  have afterRange := bonus_range 119 (HazardPattern.afterPattern 10000 p (.push 119 (.stay 120)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 119 (.stay 120))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 120))) ∧ bonus (HazardPattern.nextHero (.push 119 (.stay 120))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 120))) ≤ 2 at afterRange
  rw [gammaAfter362] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14407 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4383 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14407 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14407 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4383 p complete
    omega
theorem local362 (p : Pattern) (guard : d100940 p = 1)
    (decreasing : bonus 119 (HazardPattern.afterPattern 10000 p (.push 119 (.stay 120))) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 119 (.stay 120)) + NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 119 (.stay 120)))) + bonus 119 (HazardPattern.afterPattern 10000 p (.push 119 (.stay 120))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 119 (.stay 120)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 119 (.stay 120))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 120))) < bonus 118 p at decreasing
  rw [gammaAfter362, at118] at decreasing
  have numeric := numeric362 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 119 (.stay 120))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 120)))
  rw [oldBefore118, at118, literal, oldAfter362, gammaAfter362]
  exact numeric
theorem numeric363 (p : Pattern) (guard : d82414 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 118 p
  rw [at118] at beforeRange
  have afterRange := bonus_range 97 (HazardPattern.afterPattern 10000 p (.walk 97))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ∧ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ≤ 2 at afterRange
  rw [gammaAfter363] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9154 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9154 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9154 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local363 (p : Pattern) (guard : d82414 p = 1)
    (decreasing : bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 97) + NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 97))) + bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 97) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 118 p at decreasing
  rw [gammaAfter363, at118] at decreasing
  have numeric := numeric363 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97))
  rw [oldBefore118, at118, literal, oldAfter363, gammaAfter363]
  exact numeric
theorem numeric364 (p : Pattern) (guard : d82360 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 118 p
  rw [at118] at beforeRange
  have afterRange := bonus_range 95 (HazardPattern.afterPattern 10000 p (.walk 95))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) ∧ bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) ≤ 2 at afterRange
  rw [gammaAfter364] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9143 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9143 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9143 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local364 (p : Pattern) (guard : d82360 p = 1)
    (decreasing : bonus 95 (HazardPattern.afterPattern 10000 p (.walk 95)) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 95) + NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 95))) + bonus 95 (HazardPattern.afterPattern 10000 p (.walk 95)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 95) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) < bonus 118 p at decreasing
  rw [gammaAfter364, at118] at decreasing
  have numeric := numeric364 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95))
  rw [oldBefore118, at118, literal, oldAfter364, gammaAfter364]
  exact numeric
theorem numeric365 (p : Pattern) (guard : d100942 p = 1) (decreasing : d10648 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d48308 p + d10648 p := by
  have beforeRange := bonus_range 118 p
  rw [at118] at beforeRange
  have afterRange := bonus_range 141 (HazardPattern.afterPattern 10000 p (.walk 141))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) ∧ bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) ≤ 2 at afterRange
  rw [gammaAfter365] at afterRange
  have possibilities : (d0 p = 1 ∧ d10648 p = 0) ∨ (d0 p = 2 ∧ d10648 p = 0) ∨ (d0 p = 2 ∧ d10648 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro6801 p pair.2
    have combined := andIntro14408 p beforeEq guard
    have complete := andIntro14409 p combined afterEq
    have bound := compare10062 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro6801 p pair.2
    have combined := andIntro14408 p beforeEq guard
    have complete := andIntro14409 p combined afterEq
    have bound := compare10063 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro6896 p pair.2
    have combined := andIntro14408 p beforeEq guard
    have complete := andIntro14410 p combined afterEq
    have bound := compare10062 p complete
    omega
theorem local365 (p : Pattern) (guard : d100942 p = 1)
    (decreasing : bonus 141 (HazardPattern.afterPattern 10000 p (.walk 141)) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 141) + NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 141))) + bonus 141 (HazardPattern.afterPattern 10000 p (.walk 141)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 141) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) < bonus 118 p at decreasing
  rw [gammaAfter365, at118] at decreasing
  have numeric := numeric365 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141))
  rw [oldBefore118, at118, literal, oldAfter365, gammaAfter365]
  exact numeric
theorem numeric366 (p : Pattern) (guard : d82376 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 119 p
  rw [at119] at beforeRange
  have afterRange := bonus_range 97 (HazardPattern.afterPattern 10000 p (.walk 97))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ∧ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ≤ 2 at afterRange
  rw [gammaAfter366] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9150 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9150 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9150 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local366 (p : Pattern) (guard : d82376 p = 1)
    (decreasing : bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 97) + NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 97))) + bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 97) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 119 p at decreasing
  rw [gammaAfter366, at119] at decreasing
  have numeric := numeric366 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97))
  rw [oldBefore119, at119, literal, oldAfter366, gammaAfter366]
  exact numeric
theorem numeric367 (p : Pattern) (guard : d100941 p = 1) (decreasing : d10648 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d48308 p + d10648 p := by
  have beforeRange := bonus_range 119 p
  rw [at119] at beforeRange
  have afterRange := bonus_range 141 (HazardPattern.afterPattern 10000 p (.walk 141))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) ∧ bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) ≤ 2 at afterRange
  rw [gammaAfter367] at afterRange
  have possibilities : (d0 p = 1 ∧ d10648 p = 0) ∨ (d0 p = 2 ∧ d10648 p = 0) ∨ (d0 p = 2 ∧ d10648 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro6801 p pair.2
    have combined := andIntro14411 p beforeEq guard
    have complete := andIntro14409 p combined afterEq
    have bound := compare10062 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro6801 p pair.2
    have combined := andIntro14411 p beforeEq guard
    have complete := andIntro14409 p combined afterEq
    have bound := compare10063 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro6896 p pair.2
    have combined := andIntro14411 p beforeEq guard
    have complete := andIntro14410 p combined afterEq
    have bound := compare10062 p complete
    omega
theorem local367 (p : Pattern) (guard : d100941 p = 1)
    (decreasing : bonus 141 (HazardPattern.afterPattern 10000 p (.walk 141)) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 141) + NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 141))) + bonus 141 (HazardPattern.afterPattern 10000 p (.walk 141)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 141) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) < bonus 119 p at decreasing
  rw [gammaAfter367, at119] at decreasing
  have numeric := numeric367 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141))
  rw [oldBefore119, at119, literal, oldAfter367, gammaAfter367]
  exact numeric
theorem numeric368 (p : Pattern) (guard : d102055 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d102102 p + d0 p := by
  have beforeRange := bonus_range 119 p
  rw [at119] at beforeRange
  have afterRange := bonus_range 141 (HazardPattern.afterPattern 10000 p (.push 141 (.stay 163)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 141 (.stay 163))) (HazardPattern.afterPattern 10000 p (.push 141 (.stay 163))) ∧ bonus (HazardPattern.nextHero (.push 141 (.stay 163))) (HazardPattern.afterPattern 10000 p (.push 141 (.stay 163))) ≤ 2 at afterRange
  rw [gammaAfter368] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14412 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10064 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14412 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10065 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14412 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10064 p complete
    omega
theorem local368 (p : Pattern) (guard : d102055 p = 1)
    (decreasing : bonus 141 (HazardPattern.afterPattern 10000 p (.push 141 (.stay 163))) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 141 (.stay 163)) + NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 141 (.stay 163)))) + bonus 141 (HazardPattern.afterPattern 10000 p (.push 141 (.stay 163))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 141 (.stay 163)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 141 (.stay 163))) (HazardPattern.afterPattern 10000 p (.push 141 (.stay 163))) < bonus 119 p at decreasing
  rw [gammaAfter368, at119] at decreasing
  have numeric := numeric368 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 141 (.stay 163))) (HazardPattern.afterPattern 10000 p (.push 141 (.stay 163)))
  rw [oldBefore119, at119, literal, oldAfter368, gammaAfter368]
  exact numeric
theorem numeric369 (p : Pattern) (guard : d82407 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 119 p
  rw [at119] at beforeRange
  have afterRange := bonus_range 120 (HazardPattern.afterPattern 10000 p (.walk 120))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) ∧ bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) ≤ 2 at afterRange
  rw [gammaAfter369] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14413 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14413 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14413 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local369 (p : Pattern) (guard : d82407 p = 1)
    (decreasing : bonus 120 (HazardPattern.afterPattern 10000 p (.walk 120)) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 120) + NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 120))) + bonus 120 (HazardPattern.afterPattern 10000 p (.walk 120)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 120) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) < bonus 119 p at decreasing
  rw [gammaAfter369, at119] at decreasing
  have numeric := numeric369 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120))
  rw [oldBefore119, at119, literal, oldAfter369, gammaAfter369]
  exact numeric
theorem numeric370 (p : Pattern) (guard : d100937 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 119 p
  rw [at119] at beforeRange
  have afterRange := bonus_range 118 (HazardPattern.afterPattern 10000 p (.walk 118))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) ∧ bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) ≤ 2 at afterRange
  rw [gammaAfter370] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14406 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14406 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14406 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local370 (p : Pattern) (guard : d100937 p = 1)
    (decreasing : bonus 118 (HazardPattern.afterPattern 10000 p (.walk 118)) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 118) + NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 118))) + bonus 118 (HazardPattern.afterPattern 10000 p (.walk 118)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 118) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) < bonus 119 p at decreasing
  rw [gammaAfter370, at119] at decreasing
  have numeric := numeric370 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118))
  rw [oldBefore119, at119, literal, oldAfter370, gammaAfter370]
  exact numeric
theorem numeric371 (p : Pattern) (guard : d82422 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 119 p
  rw [at119] at beforeRange
  have afterRange := bonus_range 98 (HazardPattern.afterPattern 10000 p (.walk 98))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) ∧ bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) ≤ 2 at afterRange
  rw [gammaAfter371] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9156 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9156 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9156 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local371 (p : Pattern) (guard : d82422 p = 1)
    (decreasing : bonus 98 (HazardPattern.afterPattern 10000 p (.walk 98)) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 98) + NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 98))) + bonus 98 (HazardPattern.afterPattern 10000 p (.walk 98)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 98) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) < bonus 119 p at decreasing
  rw [gammaAfter371, at119] at decreasing
  have numeric := numeric371 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98))
  rw [oldBefore119, at119, literal, oldAfter371, gammaAfter371]
  exact numeric
theorem numeric372 (p : Pattern) (guard : d82375 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 119 p
  rw [at119] at beforeRange
  have afterRange := bonus_range 96 (HazardPattern.afterPattern 10000 p (.walk 96))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) ∧ bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) ≤ 2 at afterRange
  rw [gammaAfter372] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9149 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9149 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9149 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local372 (p : Pattern) (guard : d82375 p = 1)
    (decreasing : bonus 96 (HazardPattern.afterPattern 10000 p (.walk 96)) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 96) + NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 96))) + bonus 96 (HazardPattern.afterPattern 10000 p (.walk 96)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 96) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) < bonus 119 p at decreasing
  rw [gammaAfter372, at119] at decreasing
  have numeric := numeric372 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96))
  rw [oldBefore119, at119, literal, oldAfter372, gammaAfter372]
  exact numeric
theorem numeric373 (p : Pattern) (guard : d82415 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 120 p
  rw [at120] at beforeRange
  have afterRange := bonus_range 98 (HazardPattern.afterPattern 10000 p (.walk 98))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) ∧ bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) ≤ 2 at afterRange
  rw [gammaAfter373] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9155 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9155 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9155 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local373 (p : Pattern) (guard : d82415 p = 1)
    (decreasing : bonus 98 (HazardPattern.afterPattern 10000 p (.walk 98)) < bonus 120 p) :
    NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 120 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 98) + NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 98))) + bonus 98 (HazardPattern.afterPattern 10000 p (.walk 98)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 98) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) < bonus 120 p at decreasing
  rw [gammaAfter373, at120] at decreasing
  have numeric := numeric373 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98))
  rw [oldBefore120, at120, literal, oldAfter373, gammaAfter373]
  exact numeric
theorem numeric374 (p : Pattern) (guard : d74072 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 120 p
  rw [at120] at beforeRange
  have afterRange := bonus_range 98 (HazardPattern.afterPattern 10000 p (.push 98 (.stay 76)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 98 (.stay 76))) (HazardPattern.afterPattern 10000 p (.push 98 (.stay 76))) ∧ bonus (HazardPattern.nextHero (.push 98 (.stay 76))) (HazardPattern.afterPattern 10000 p (.push 98 (.stay 76))) ≤ 2 at afterRange
  rw [gammaAfter374] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6781 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6781 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6781 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local374 (p : Pattern) (guard : d74072 p = 1)
    (decreasing : bonus 98 (HazardPattern.afterPattern 10000 p (.push 98 (.stay 76))) < bonus 120 p) :
    NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 120 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 98 (.stay 76)) + NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 98 (.stay 76)))) + bonus 98 (HazardPattern.afterPattern 10000 p (.push 98 (.stay 76))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 98 (.stay 76)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 98 (.stay 76))) (HazardPattern.afterPattern 10000 p (.push 98 (.stay 76))) < bonus 120 p at decreasing
  rw [gammaAfter374, at120] at decreasing
  have numeric := numeric374 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 98 (.stay 76))) (HazardPattern.afterPattern 10000 p (.push 98 (.stay 76)))
  rw [oldBefore120, at120, literal, oldAfter374, gammaAfter374]
  exact numeric
theorem numeric375 (p : Pattern) (guard : d82407 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 120 p
  rw [at120] at beforeRange
  have afterRange := bonus_range 119 (HazardPattern.afterPattern 10000 p (.walk 119))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) ∧ bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) ≤ 2 at afterRange
  rw [gammaAfter375] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14413 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14413 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14413 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local375 (p : Pattern) (guard : d82407 p = 1)
    (decreasing : bonus 119 (HazardPattern.afterPattern 10000 p (.walk 119)) < bonus 120 p) :
    NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 120 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 119) + NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 119))) + bonus 119 (HazardPattern.afterPattern 10000 p (.walk 119)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 119) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) < bonus 120 p at decreasing
  rw [gammaAfter375, at120] at decreasing
  have numeric := numeric375 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119))
  rw [oldBefore120, at120, literal, oldAfter375, gammaAfter375]
  exact numeric
theorem numeric376 (p : Pattern) (guard : d100940 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (2 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 120 p
  rw [at120] at beforeRange
  have afterRange := bonus_range 119 (HazardPattern.afterPattern 10000 p (.push 119 (.stay 118)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 119 (.stay 118))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 118))) ∧ bonus (HazardPattern.nextHero (.push 119 (.stay 118))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 118))) ≤ 2 at afterRange
  rw [gammaAfter376] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14407 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4383 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14407 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14407 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4383 p complete
    omega
theorem local376 (p : Pattern) (guard : d100940 p = 1)
    (decreasing : bonus 119 (HazardPattern.afterPattern 10000 p (.push 119 (.stay 118))) < bonus 120 p) :
    NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 120 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 119 (.stay 118)) + NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 119 (.stay 118)))) + bonus 119 (HazardPattern.afterPattern 10000 p (.push 119 (.stay 118))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 119 (.stay 118)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 119 (.stay 118))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 118))) < bonus 120 p at decreasing
  rw [gammaAfter376, at120] at decreasing
  have numeric := numeric376 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 119 (.stay 118))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 118)))
  rw [oldBefore120, at120, literal, oldAfter376, gammaAfter376]
  exact numeric
theorem numeric377 (p : Pattern) (guard : d82409 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 120 p
  rw [at120] at beforeRange
  have afterRange := bonus_range 97 (HazardPattern.afterPattern 10000 p (.walk 97))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ∧ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ≤ 2 at afterRange
  rw [gammaAfter377] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9153 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9153 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9153 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local377 (p : Pattern) (guard : d82409 p = 1)
    (decreasing : bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 120 p) :
    NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 120 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 97) + NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 97))) + bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 97) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 120 p at decreasing
  rw [gammaAfter377, at120] at decreasing
  have numeric := numeric377 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97))
  rw [oldBefore120, at120, literal, oldAfter377, gammaAfter377]
  exact numeric
theorem numeric378 (p : Pattern) (guard : d102105 p = 1) (decreasing : d10648 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d48308 p + d10648 p := by
  have beforeRange := bonus_range 120 p
  rw [at120] at beforeRange
  have afterRange := bonus_range 141 (HazardPattern.afterPattern 10000 p (.walk 141))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) ∧ bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) ≤ 2 at afterRange
  rw [gammaAfter378] at afterRange
  have possibilities : (d0 p = 1 ∧ d10648 p = 0) ∨ (d0 p = 2 ∧ d10648 p = 0) ∨ (d0 p = 2 ∧ d10648 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro6801 p pair.2
    have combined := andIntro14414 p beforeEq guard
    have complete := andIntro14409 p combined afterEq
    have bound := compare10062 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro6801 p pair.2
    have combined := andIntro14414 p beforeEq guard
    have complete := andIntro14409 p combined afterEq
    have bound := compare10063 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro6896 p pair.2
    have combined := andIntro14414 p beforeEq guard
    have complete := andIntro14410 p combined afterEq
    have bound := compare10062 p complete
    omega
theorem local378 (p : Pattern) (guard : d102105 p = 1)
    (decreasing : bonus 141 (HazardPattern.afterPattern 10000 p (.walk 141)) < bonus 120 p) :
    NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 120 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 141) + NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 141))) + bonus 141 (HazardPattern.afterPattern 10000 p (.walk 141)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 141) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) < bonus 120 p at decreasing
  rw [gammaAfter378, at120] at decreasing
  have numeric := numeric378 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141))
  rw [oldBefore120, at120, literal, oldAfter378, gammaAfter378]
  exact numeric
theorem numeric379 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 122 p
  rw [at122] at beforeRange
  have afterRange := bonus_range 100 (HazardPattern.afterPattern 10000 p (.walk 100))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) ∧ bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) ≤ 2 at afterRange
  rw [gammaAfter379] at afterRange
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
theorem local379 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 100 (HazardPattern.afterPattern 10000 p (.walk 100)) < bonus 122 p) :
    NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 122 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 100) + NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 100))) + bonus 100 (HazardPattern.afterPattern 10000 p (.walk 100)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 100) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) < bonus 122 p at decreasing
  rw [gammaAfter379, at122] at decreasing
  have numeric := numeric379 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100))
  rw [oldBefore122, at122, literal, oldAfter379, gammaAfter379]
  exact numeric
theorem numeric380 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 122 p
  rw [at122] at beforeRange
  have afterRange := bonus_range 100 (HazardPattern.afterPattern 10000 p (.push 100 (.stay 78)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 100 (.stay 78))) (HazardPattern.afterPattern 10000 p (.push 100 (.stay 78))) ∧ bonus (HazardPattern.nextHero (.push 100 (.stay 78))) (HazardPattern.afterPattern 10000 p (.push 100 (.stay 78))) ≤ 2 at afterRange
  rw [gammaAfter380] at afterRange
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
theorem local380 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 100 (HazardPattern.afterPattern 10000 p (.push 100 (.stay 78))) < bonus 122 p) :
    NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 122 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 100 (.stay 78)) + NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 100 (.stay 78)))) + bonus 100 (HazardPattern.afterPattern 10000 p (.push 100 (.stay 78))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 100 (.stay 78)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 100 (.stay 78))) (HazardPattern.afterPattern 10000 p (.push 100 (.stay 78))) < bonus 122 p at decreasing
  rw [gammaAfter380, at122] at decreasing
  have numeric := numeric380 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 100 (.stay 78))) (HazardPattern.afterPattern 10000 p (.push 100 (.stay 78)))
  rw [oldBefore122, at122, literal, oldAfter380, gammaAfter380]
  exact numeric
theorem numeric381 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 122 p
  rw [at122] at beforeRange
  have afterRange := bonus_range 144 (HazardPattern.afterPattern 10000 p (.walk 144))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) ∧ bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) ≤ 2 at afterRange
  rw [gammaAfter381] at afterRange
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
theorem local381 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 144 (HazardPattern.afterPattern 10000 p (.walk 144)) < bonus 122 p) :
    NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 122 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 144) + NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 144))) + bonus 144 (HazardPattern.afterPattern 10000 p (.walk 144)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 144) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) < bonus 122 p at decreasing
  rw [gammaAfter381, at122] at decreasing
  have numeric := numeric381 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144))
  rw [oldBefore122, at122, literal, oldAfter381, gammaAfter381]
  exact numeric
theorem numeric382 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 122 p
  rw [at122] at beforeRange
  have afterRange := bonus_range 144 (HazardPattern.afterPattern 10000 p (.push 144 (.stay 166)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 144 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 144 (.stay 166))) ∧ bonus (HazardPattern.nextHero (.push 144 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 144 (.stay 166))) ≤ 2 at afterRange
  rw [gammaAfter382] at afterRange
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
theorem local382 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 144 (HazardPattern.afterPattern 10000 p (.push 144 (.stay 166))) < bonus 122 p) :
    NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 122 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 144 (.stay 166)) + NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 144 (.stay 166)))) + bonus 144 (HazardPattern.afterPattern 10000 p (.push 144 (.stay 166))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 144 (.stay 166)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 144 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 144 (.stay 166))) < bonus 122 p at decreasing
  rw [gammaAfter382, at122] at decreasing
  have numeric := numeric382 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 144 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 144 (.stay 166)))
  rw [oldBefore122, at122, literal, oldAfter382, gammaAfter382]
  exact numeric
theorem numeric383 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 122 p
  rw [at122] at beforeRange
  have afterRange := bonus_range 123 (HazardPattern.afterPattern 10000 p (.walk 123))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ∧ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ≤ 2 at afterRange
  rw [gammaAfter383] at afterRange
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
theorem local383 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 122 p) :
    NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 122 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 123) + NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) + bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 123) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 122 p at decreasing
  rw [gammaAfter383, at122] at decreasing
  have numeric := numeric383 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123))
  rw [oldBefore122, at122, literal, oldAfter383, gammaAfter383]
  exact numeric
theorem numeric384 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 122 p
  rw [at122] at beforeRange
  have afterRange := bonus_range 123 (HazardPattern.afterPattern 10000 p (.push 123 (.stay 124)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 123 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 124))) ∧ bonus (HazardPattern.nextHero (.push 123 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 124))) ≤ 2 at afterRange
  rw [gammaAfter384] at afterRange
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
theorem local384 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 123 (HazardPattern.afterPattern 10000 p (.push 123 (.stay 124))) < bonus 122 p) :
    NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 122 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 123 (.stay 124)) + NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 123 (.stay 124)))) + bonus 123 (HazardPattern.afterPattern 10000 p (.push 123 (.stay 124))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 123 (.stay 124)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 123 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 124))) < bonus 122 p at decreasing
  rw [gammaAfter384, at122] at decreasing
  have numeric := numeric384 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 123 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 124)))
  rw [oldBefore122, at122, literal, oldAfter384, gammaAfter384]
  exact numeric
theorem numeric385 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 122 p
  rw [at122] at beforeRange
  have afterRange := bonus_range 101 (HazardPattern.afterPattern 10000 p (.walk 101))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ∧ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ≤ 2 at afterRange
  rw [gammaAfter385] at afterRange
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
theorem local385 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 122 p) :
    NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 122 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 101) + NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 101))) + bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 101) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 122 p at decreasing
  rw [gammaAfter385, at122] at decreasing
  have numeric := numeric385 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101))
  rw [oldBefore122, at122, literal, oldAfter385, gammaAfter385]
  exact numeric
theorem numeric386 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 122 p
  rw [at122] at beforeRange
  have afterRange := bonus_range 145 (HazardPattern.afterPattern 10000 p (.walk 145))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ∧ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ≤ 2 at afterRange
  rw [gammaAfter386] at afterRange
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
theorem local386 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 122 p) :
    NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 122 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 145) + NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) + bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 145) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 122 p at decreasing
  rw [gammaAfter386, at122] at decreasing
  have numeric := numeric386 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145))
  rw [oldBefore122, at122, literal, oldAfter386, gammaAfter386]
  exact numeric
theorem numeric387 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 123 p
  rw [at123] at beforeRange
  have afterRange := bonus_range 101 (HazardPattern.afterPattern 10000 p (.walk 101))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ∧ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ≤ 2 at afterRange
  rw [gammaAfter387] at afterRange
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
theorem local387 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 123 p) :
    NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 123 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 101) + NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 101))) + bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 101) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 123 p at decreasing
  rw [gammaAfter387, at123] at decreasing
  have numeric := numeric387 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101))
  rw [oldBefore123, at123, literal, oldAfter387, gammaAfter387]
  exact numeric
theorem numeric388 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 123 p
  rw [at123] at beforeRange
  have afterRange := bonus_range 101 (HazardPattern.afterPattern 10000 p (.push 101 (.stay 79)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 101 (.stay 79))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 79))) ∧ bonus (HazardPattern.nextHero (.push 101 (.stay 79))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 79))) ≤ 2 at afterRange
  rw [gammaAfter388] at afterRange
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
theorem local388 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 101 (HazardPattern.afterPattern 10000 p (.push 101 (.stay 79))) < bonus 123 p) :
    NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 123 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 101 (.stay 79)) + NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 101 (.stay 79)))) + bonus 101 (HazardPattern.afterPattern 10000 p (.push 101 (.stay 79))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 101 (.stay 79)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 101 (.stay 79))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 79))) < bonus 123 p at decreasing
  rw [gammaAfter388, at123] at decreasing
  have numeric := numeric388 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 101 (.stay 79))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 79)))
  rw [oldBefore123, at123, literal, oldAfter388, gammaAfter388]
  exact numeric
theorem numeric389 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 123 p
  rw [at123] at beforeRange
  have afterRange := bonus_range 145 (HazardPattern.afterPattern 10000 p (.walk 145))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ∧ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ≤ 2 at afterRange
  rw [gammaAfter389] at afterRange
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
theorem local389 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 123 p) :
    NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 123 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 145) + NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) + bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 145) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 123 p at decreasing
  rw [gammaAfter389, at123] at decreasing
  have numeric := numeric389 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145))
  rw [oldBefore123, at123, literal, oldAfter389, gammaAfter389]
  exact numeric
theorem numeric390 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 123 p
  rw [at123] at beforeRange
  have afterRange := bonus_range 145 (HazardPattern.afterPattern 10000 p (.push 145 (.stay 167)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 145 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 167))) ∧ bonus (HazardPattern.nextHero (.push 145 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 167))) ≤ 2 at afterRange
  rw [gammaAfter390] at afterRange
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
theorem local390 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 145 (HazardPattern.afterPattern 10000 p (.push 145 (.stay 167))) < bonus 123 p) :
    NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 123 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 145 (.stay 167)) + NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 145 (.stay 167)))) + bonus 145 (HazardPattern.afterPattern 10000 p (.push 145 (.stay 167))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 145 (.stay 167)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 145 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 167))) < bonus 123 p at decreasing
  rw [gammaAfter390, at123] at decreasing
  have numeric := numeric390 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 145 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 167)))
  rw [oldBefore123, at123, literal, oldAfter390, gammaAfter390]
  exact numeric
theorem numeric391 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 123 p
  rw [at123] at beforeRange
  have afterRange := bonus_range 124 (HazardPattern.afterPattern 10000 p (.walk 124))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ∧ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ≤ 2 at afterRange
  rw [gammaAfter391] at afterRange
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
theorem local391 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 123 p) :
    NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 123 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 124) + NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) + bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 124) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 123 p at decreasing
  rw [gammaAfter391, at123] at decreasing
  have numeric := numeric391 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124))
  rw [oldBefore123, at123, literal, oldAfter391, gammaAfter391]
  exact numeric
theorem numeric392 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 123 p
  rw [at123] at beforeRange
  have afterRange := bonus_range 124 (HazardPattern.afterPattern 10000 p (.push 124 (.stay 125)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 124 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 125))) ∧ bonus (HazardPattern.nextHero (.push 124 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 125))) ≤ 2 at afterRange
  rw [gammaAfter392] at afterRange
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
theorem local392 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 124 (HazardPattern.afterPattern 10000 p (.push 124 (.stay 125))) < bonus 123 p) :
    NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 123 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 124 (.stay 125)) + NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 124 (.stay 125)))) + bonus 124 (HazardPattern.afterPattern 10000 p (.push 124 (.stay 125))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 124 (.stay 125)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 124 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 125))) < bonus 123 p at decreasing
  rw [gammaAfter392, at123] at decreasing
  have numeric := numeric392 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 124 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 125)))
  rw [oldBefore123, at123, literal, oldAfter392, gammaAfter392]
  exact numeric
theorem numeric393 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 123 p
  rw [at123] at beforeRange
  have afterRange := bonus_range 122 (HazardPattern.afterPattern 10000 p (.walk 122))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) ∧ bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) ≤ 2 at afterRange
  rw [gammaAfter393] at afterRange
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
theorem local393 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 122 (HazardPattern.afterPattern 10000 p (.walk 122)) < bonus 123 p) :
    NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 123 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 122) + NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 122))) + bonus 122 (HazardPattern.afterPattern 10000 p (.walk 122)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 122) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) < bonus 123 p at decreasing
  rw [gammaAfter393, at123] at decreasing
  have numeric := numeric393 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122))
  rw [oldBefore123, at123, literal, oldAfter393, gammaAfter393]
  exact numeric
theorem numeric394 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 123 p
  rw [at123] at beforeRange
  have afterRange := bonus_range 102 (HazardPattern.afterPattern 10000 p (.walk 102))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ∧ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ≤ 2 at afterRange
  rw [gammaAfter394] at afterRange
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
theorem local394 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 123 p) :
    NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 123 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 102) + NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 102))) + bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 102) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 123 p at decreasing
  rw [gammaAfter394, at123] at decreasing
  have numeric := numeric394 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102))
  rw [oldBefore123, at123, literal, oldAfter394, gammaAfter394]
  exact numeric
theorem numeric395 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 123 p
  rw [at123] at beforeRange
  have afterRange := bonus_range 100 (HazardPattern.afterPattern 10000 p (.walk 100))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) ∧ bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) ≤ 2 at afterRange
  rw [gammaAfter395] at afterRange
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
theorem local395 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 100 (HazardPattern.afterPattern 10000 p (.walk 100)) < bonus 123 p) :
    NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 123 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 100) + NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 100))) + bonus 100 (HazardPattern.afterPattern 10000 p (.walk 100)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 100) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) < bonus 123 p at decreasing
  rw [gammaAfter395, at123] at decreasing
  have numeric := numeric395 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100))
  rw [oldBefore123, at123, literal, oldAfter395, gammaAfter395]
  exact numeric
theorem numeric396 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 123 p
  rw [at123] at beforeRange
  have afterRange := bonus_range 146 (HazardPattern.afterPattern 10000 p (.walk 146))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ∧ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ≤ 2 at afterRange
  rw [gammaAfter396] at afterRange
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
theorem local396 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 123 p) :
    NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 123 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 146) + NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) + bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 146) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 123 p at decreasing
  rw [gammaAfter396, at123] at decreasing
  have numeric := numeric396 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146))
  rw [oldBefore123, at123, literal, oldAfter396, gammaAfter396]
  exact numeric
theorem numeric397 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 123 p
  rw [at123] at beforeRange
  have afterRange := bonus_range 144 (HazardPattern.afterPattern 10000 p (.walk 144))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) ∧ bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) ≤ 2 at afterRange
  rw [gammaAfter397] at afterRange
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
theorem local397 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 144 (HazardPattern.afterPattern 10000 p (.walk 144)) < bonus 123 p) :
    NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 123 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 144) + NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 144))) + bonus 144 (HazardPattern.afterPattern 10000 p (.walk 144)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 144) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) < bonus 123 p at decreasing
  rw [gammaAfter397, at123] at decreasing
  have numeric := numeric397 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144))
  rw [oldBefore123, at123, literal, oldAfter397, gammaAfter397]
  exact numeric
theorem numeric398 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 124 p
  rw [at124] at beforeRange
  have afterRange := bonus_range 102 (HazardPattern.afterPattern 10000 p (.walk 102))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ∧ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ≤ 2 at afterRange
  rw [gammaAfter398] at afterRange
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
theorem local398 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 102) + NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 102))) + bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 102) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 124 p at decreasing
  rw [gammaAfter398, at124] at decreasing
  have numeric := numeric398 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102))
  rw [oldBefore124, at124, literal, oldAfter398, gammaAfter398]
  exact numeric
theorem numeric399 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 124 p
  rw [at124] at beforeRange
  have afterRange := bonus_range 102 (HazardPattern.afterPattern 10000 p (.push 102 (.stay 80)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 102 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 80))) ∧ bonus (HazardPattern.nextHero (.push 102 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 80))) ≤ 2 at afterRange
  rw [gammaAfter399] at afterRange
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
theorem local399 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 102 (HazardPattern.afterPattern 10000 p (.push 102 (.stay 80))) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 102 (.stay 80)) + NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 102 (.stay 80)))) + bonus 102 (HazardPattern.afterPattern 10000 p (.push 102 (.stay 80))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 102 (.stay 80)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 102 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 80))) < bonus 124 p at decreasing
  rw [gammaAfter399, at124] at decreasing
  have numeric := numeric399 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 102 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 80)))
  rw [oldBefore124, at124, literal, oldAfter399, gammaAfter399]
  exact numeric
theorem numeric400 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 124 p
  rw [at124] at beforeRange
  have afterRange := bonus_range 146 (HazardPattern.afterPattern 10000 p (.walk 146))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ∧ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ≤ 2 at afterRange
  rw [gammaAfter400] at afterRange
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
theorem local400 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 146) + NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) + bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 146) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 124 p at decreasing
  rw [gammaAfter400, at124] at decreasing
  have numeric := numeric400 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146))
  rw [oldBefore124, at124, literal, oldAfter400, gammaAfter400]
  exact numeric
theorem numeric401 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 124 p
  rw [at124] at beforeRange
  have afterRange := bonus_range 146 (HazardPattern.afterPattern 10000 p (.push 146 (.stay 168)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 146 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 168))) ∧ bonus (HazardPattern.nextHero (.push 146 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 168))) ≤ 2 at afterRange
  rw [gammaAfter401] at afterRange
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
theorem local401 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 146 (HazardPattern.afterPattern 10000 p (.push 146 (.stay 168))) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 146 (.stay 168)) + NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 146 (.stay 168)))) + bonus 146 (HazardPattern.afterPattern 10000 p (.push 146 (.stay 168))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 146 (.stay 168)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 146 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 168))) < bonus 124 p at decreasing
  rw [gammaAfter401, at124] at decreasing
  have numeric := numeric401 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 146 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 168)))
  rw [oldBefore124, at124, literal, oldAfter401, gammaAfter401]
  exact numeric
theorem numeric402 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 124 p
  rw [at124] at beforeRange
  have afterRange := bonus_range 125 (HazardPattern.afterPattern 10000 p (.walk 125))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ∧ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ≤ 2 at afterRange
  rw [gammaAfter402] at afterRange
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
theorem local402 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 125) + NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) + bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 125) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 124 p at decreasing
  rw [gammaAfter402, at124] at decreasing
  have numeric := numeric402 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125))
  rw [oldBefore124, at124, literal, oldAfter402, gammaAfter402]
  exact numeric
theorem numeric403 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 124 p
  rw [at124] at beforeRange
  have afterRange := bonus_range 125 (HazardPattern.afterPattern 10000 p (.push 125 (.stay 126)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 125 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 126))) ∧ bonus (HazardPattern.nextHero (.push 125 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 126))) ≤ 2 at afterRange
  rw [gammaAfter403] at afterRange
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
theorem local403 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 125 (HazardPattern.afterPattern 10000 p (.push 125 (.stay 126))) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 125 (.stay 126)) + NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 125 (.stay 126)))) + bonus 125 (HazardPattern.afterPattern 10000 p (.push 125 (.stay 126))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 125 (.stay 126)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 125 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 126))) < bonus 124 p at decreasing
  rw [gammaAfter403, at124] at decreasing
  have numeric := numeric403 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 125 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 126)))
  rw [oldBefore124, at124, literal, oldAfter403, gammaAfter403]
  exact numeric
theorem numeric404 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 124 p
  rw [at124] at beforeRange
  have afterRange := bonus_range 123 (HazardPattern.afterPattern 10000 p (.walk 123))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ∧ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ≤ 2 at afterRange
  rw [gammaAfter404] at afterRange
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
theorem local404 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 123) + NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) + bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 123) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 124 p at decreasing
  rw [gammaAfter404, at124] at decreasing
  have numeric := numeric404 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123))
  rw [oldBefore124, at124, literal, oldAfter404, gammaAfter404]
  exact numeric
theorem numeric405 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 124 p
  rw [at124] at beforeRange
  have afterRange := bonus_range 123 (HazardPattern.afterPattern 10000 p (.push 123 (.stay 122)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 123 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 122))) ∧ bonus (HazardPattern.nextHero (.push 123 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 122))) ≤ 2 at afterRange
  rw [gammaAfter405] at afterRange
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
theorem local405 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 123 (HazardPattern.afterPattern 10000 p (.push 123 (.stay 122))) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 123 (.stay 122)) + NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 123 (.stay 122)))) + bonus 123 (HazardPattern.afterPattern 10000 p (.push 123 (.stay 122))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 123 (.stay 122)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 123 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 122))) < bonus 124 p at decreasing
  rw [gammaAfter405, at124] at decreasing
  have numeric := numeric405 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 123 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 122)))
  rw [oldBefore124, at124, literal, oldAfter405, gammaAfter405]
  exact numeric
theorem numeric406 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 124 p
  rw [at124] at beforeRange
  have afterRange := bonus_range 103 (HazardPattern.afterPattern 10000 p (.walk 103))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ∧ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ≤ 2 at afterRange
  rw [gammaAfter406] at afterRange
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
theorem local406 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 103) + NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 103))) + bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 103) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 124 p at decreasing
  rw [gammaAfter406, at124] at decreasing
  have numeric := numeric406 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103))
  rw [oldBefore124, at124, literal, oldAfter406, gammaAfter406]
  exact numeric
theorem numeric407 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 124 p
  rw [at124] at beforeRange
  have afterRange := bonus_range 101 (HazardPattern.afterPattern 10000 p (.walk 101))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ∧ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ≤ 2 at afterRange
  rw [gammaAfter407] at afterRange
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
theorem local407 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 101) + NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 101))) + bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 101) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 124 p at decreasing
  rw [gammaAfter407, at124] at decreasing
  have numeric := numeric407 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101))
  rw [oldBefore124, at124, literal, oldAfter407, gammaAfter407]
  exact numeric
theorem numeric408 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 124 p
  rw [at124] at beforeRange
  have afterRange := bonus_range 147 (HazardPattern.afterPattern 10000 p (.walk 147))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ∧ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ≤ 2 at afterRange
  rw [gammaAfter408] at afterRange
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
theorem local408 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 147) + NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) + bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 147) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 124 p at decreasing
  rw [gammaAfter408, at124] at decreasing
  have numeric := numeric408 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147))
  rw [oldBefore124, at124, literal, oldAfter408, gammaAfter408]
  exact numeric
theorem numeric409 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 124 p
  rw [at124] at beforeRange
  have afterRange := bonus_range 145 (HazardPattern.afterPattern 10000 p (.walk 145))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ∧ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ≤ 2 at afterRange
  rw [gammaAfter409] at afterRange
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
theorem local409 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 145) + NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) + bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 145) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 124 p at decreasing
  rw [gammaAfter409, at124] at decreasing
  have numeric := numeric409 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145))
  rw [oldBefore124, at124, literal, oldAfter409, gammaAfter409]
  exact numeric
theorem numeric410 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 125 p
  rw [at125] at beforeRange
  have afterRange := bonus_range 103 (HazardPattern.afterPattern 10000 p (.walk 103))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ∧ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ≤ 2 at afterRange
  rw [gammaAfter410] at afterRange
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
theorem local410 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 103) + NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 103))) + bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 103) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 125 p at decreasing
  rw [gammaAfter410, at125] at decreasing
  have numeric := numeric410 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103))
  rw [oldBefore125, at125, literal, oldAfter410, gammaAfter410]
  exact numeric
theorem numeric411 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 125 p
  rw [at125] at beforeRange
  have afterRange := bonus_range 103 (HazardPattern.afterPattern 10000 p (.push 103 (.stay 81)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 103 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 81))) ∧ bonus (HazardPattern.nextHero (.push 103 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 81))) ≤ 2 at afterRange
  rw [gammaAfter411] at afterRange
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
theorem local411 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 103 (HazardPattern.afterPattern 10000 p (.push 103 (.stay 81))) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 103 (.stay 81)) + NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 103 (.stay 81)))) + bonus 103 (HazardPattern.afterPattern 10000 p (.push 103 (.stay 81))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 103 (.stay 81)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 103 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 81))) < bonus 125 p at decreasing
  rw [gammaAfter411, at125] at decreasing
  have numeric := numeric411 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 103 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 81)))
  rw [oldBefore125, at125, literal, oldAfter411, gammaAfter411]
  exact numeric
theorem numeric412 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 125 p
  rw [at125] at beforeRange
  have afterRange := bonus_range 147 (HazardPattern.afterPattern 10000 p (.walk 147))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ∧ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ≤ 2 at afterRange
  rw [gammaAfter412] at afterRange
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
theorem local412 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 147) + NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) + bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 147) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 125 p at decreasing
  rw [gammaAfter412, at125] at decreasing
  have numeric := numeric412 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147))
  rw [oldBefore125, at125, literal, oldAfter412, gammaAfter412]
  exact numeric
theorem numeric413 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 125 p
  rw [at125] at beforeRange
  have afterRange := bonus_range 147 (HazardPattern.afterPattern 10000 p (.push 147 (.stay 169)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 147 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 169))) ∧ bonus (HazardPattern.nextHero (.push 147 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 169))) ≤ 2 at afterRange
  rw [gammaAfter413] at afterRange
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
theorem local413 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 147 (HazardPattern.afterPattern 10000 p (.push 147 (.stay 169))) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 147 (.stay 169)) + NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 147 (.stay 169)))) + bonus 147 (HazardPattern.afterPattern 10000 p (.push 147 (.stay 169))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 147 (.stay 169)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 147 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 169))) < bonus 125 p at decreasing
  rw [gammaAfter413, at125] at decreasing
  have numeric := numeric413 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 147 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 169)))
  rw [oldBefore125, at125, literal, oldAfter413, gammaAfter413]
  exact numeric
theorem numeric414 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 125 p
  rw [at125] at beforeRange
  have afterRange := bonus_range 126 (HazardPattern.afterPattern 10000 p (.walk 126))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ∧ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ≤ 2 at afterRange
  rw [gammaAfter414] at afterRange
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
theorem local414 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 126) + NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 126))) + bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 126) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 125 p at decreasing
  rw [gammaAfter414, at125] at decreasing
  have numeric := numeric414 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126))
  rw [oldBefore125, at125, literal, oldAfter414, gammaAfter414]
  exact numeric
theorem numeric415 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 125 p
  rw [at125] at beforeRange
  have afterRange := bonus_range 126 (HazardPattern.afterPattern 10000 p (.push 126 (.stay 127)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 126 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 127))) ∧ bonus (HazardPattern.nextHero (.push 126 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 127))) ≤ 2 at afterRange
  rw [gammaAfter415] at afterRange
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
theorem local415 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 126 (HazardPattern.afterPattern 10000 p (.push 126 (.stay 127))) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 126 (.stay 127)) + NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 126 (.stay 127)))) + bonus 126 (HazardPattern.afterPattern 10000 p (.push 126 (.stay 127))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 126 (.stay 127)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 126 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 127))) < bonus 125 p at decreasing
  rw [gammaAfter415, at125] at decreasing
  have numeric := numeric415 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 126 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 127)))
  rw [oldBefore125, at125, literal, oldAfter415, gammaAfter415]
  exact numeric
theorem numeric416 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 125 p
  rw [at125] at beforeRange
  have afterRange := bonus_range 124 (HazardPattern.afterPattern 10000 p (.walk 124))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ∧ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ≤ 2 at afterRange
  rw [gammaAfter416] at afterRange
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
theorem local416 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 124) + NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) + bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 124) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 125 p at decreasing
  rw [gammaAfter416, at125] at decreasing
  have numeric := numeric416 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124))
  rw [oldBefore125, at125, literal, oldAfter416, gammaAfter416]
  exact numeric
theorem numeric417 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 125 p
  rw [at125] at beforeRange
  have afterRange := bonus_range 124 (HazardPattern.afterPattern 10000 p (.push 124 (.stay 123)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 124 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 123))) ∧ bonus (HazardPattern.nextHero (.push 124 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 123))) ≤ 2 at afterRange
  rw [gammaAfter417] at afterRange
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
theorem local417 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 124 (HazardPattern.afterPattern 10000 p (.push 124 (.stay 123))) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 124 (.stay 123)) + NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 124 (.stay 123)))) + bonus 124 (HazardPattern.afterPattern 10000 p (.push 124 (.stay 123))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 124 (.stay 123)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 124 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 123))) < bonus 125 p at decreasing
  rw [gammaAfter417, at125] at decreasing
  have numeric := numeric417 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 124 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 123)))
  rw [oldBefore125, at125, literal, oldAfter417, gammaAfter417]
  exact numeric
theorem numeric418 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 125 p
  rw [at125] at beforeRange
  have afterRange := bonus_range 104 (HazardPattern.afterPattern 10000 p (.walk 104))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ∧ bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) ≤ 2 at afterRange
  rw [gammaAfter418] at afterRange
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
theorem local418 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 104) + NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 104))) + bonus 104 (HazardPattern.afterPattern 10000 p (.walk 104)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 104) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) < bonus 125 p at decreasing
  rw [gammaAfter418, at125] at decreasing
  have numeric := numeric418 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104))
  rw [oldBefore125, at125, literal, oldAfter418, gammaAfter418]
  exact numeric
theorem numeric419 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 125 p
  rw [at125] at beforeRange
  have afterRange := bonus_range 102 (HazardPattern.afterPattern 10000 p (.walk 102))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ∧ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ≤ 2 at afterRange
  rw [gammaAfter419] at afterRange
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
theorem local419 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 102) + NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 102))) + bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 102) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 125 p at decreasing
  rw [gammaAfter419, at125] at decreasing
  have numeric := numeric419 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102))
  rw [oldBefore125, at125, literal, oldAfter419, gammaAfter419]
  exact numeric
end NetHack.Soko22Hazard87
