import NetHack.Soko22Hazard87.Numeric014
import NetHack.Soko22Hazard87.AndIntroBlocks0433
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric1050 (p : Pattern) (guard : d381243 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 259 p
  rw [at259] at beforeRange
  have afterRange := bonus_range 258 (HazardPattern.afterPattern 10000 p (.push 258 (.stay 257)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 258 (.stay 257))) (HazardPattern.afterPattern 10000 p (.push 258 (.stay 257))) ∧ bonus (HazardPattern.nextHero (.push 258 (.stay 257))) (HazardPattern.afterPattern 10000 p (.push 258 (.stay 257))) ≤ 2 at afterRange
  rw [gammaAfter1050] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108279 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108279 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108279 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1050 (p : Pattern) (guard : d381243 p = 1)
    (decreasing : bonus 258 (HazardPattern.afterPattern 10000 p (.push 258 (.stay 257))) < bonus 259 p) :
    NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 259 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 258 (.stay 257)) + NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 258 (.stay 257)))) + bonus 258 (HazardPattern.afterPattern 10000 p (.push 258 (.stay 257))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 258 (.stay 257)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 258 (.stay 257))) (HazardPattern.afterPattern 10000 p (.push 258 (.stay 257))) < bonus 259 p at decreasing
  rw [gammaAfter1050, at259] at decreasing
  have numeric := numeric1050 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 258 (.stay 257))) (HazardPattern.afterPattern 10000 p (.push 258 (.stay 257)))
  rw [oldBefore259, at259, literal, oldAfter1050, gammaAfter1050]
  exact numeric
theorem numeric1051 (p : Pattern) (guard : d381376 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (0 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 260 p
  rw [at260] at beforeRange
  have afterRange := bonus_range 259 (HazardPattern.afterPattern 10000 p (.walk 259))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 259)) (HazardPattern.afterPattern 10000 p (.walk 259)) ∧ bonus (HazardPattern.nextHero (.walk 259)) (HazardPattern.afterPattern 10000 p (.walk 259)) ≤ 2 at afterRange
  rw [gammaAfter1051] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108288 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108288 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108288 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare41207 p complete
    omega
theorem local1051 (p : Pattern) (guard : d381376 p = 1)
    (decreasing : bonus 259 (HazardPattern.afterPattern 10000 p (.walk 259)) < bonus 260 p) :
    NetHack.Sokoban22Refined85.bonus 260 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 260 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 259) + NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 259))) + bonus 259 (HazardPattern.afterPattern 10000 p (.walk 259)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 259) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 259)) (HazardPattern.afterPattern 10000 p (.walk 259)) < bonus 260 p at decreasing
  rw [gammaAfter1051, at260] at decreasing
  have numeric := numeric1051 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 259)) (HazardPattern.afterPattern 10000 p (.walk 259))
  rw [oldBefore260, at260, literal, oldAfter1051, gammaAfter1051]
  exact numeric
theorem numeric1052 (p : Pattern) (guard : d381391 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 260 p
  rw [at260] at beforeRange
  have afterRange := bonus_range 259 (HazardPattern.afterPattern 10000 p (.push 259 (.fill 258)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 259 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 259 (.fill 258))) ∧ bonus (HazardPattern.nextHero (.push 259 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 259 (.fill 258))) ≤ 2 at afterRange
  rw [gammaAfter1052] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108290 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108290 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108290 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1052 (p : Pattern) (guard : d381391 p = 1)
    (decreasing : bonus 259 (HazardPattern.afterPattern 10000 p (.push 259 (.fill 258))) < bonus 260 p) :
    NetHack.Sokoban22Refined85.bonus 260 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 260 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 259 (.fill 258)) + NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 259 (.fill 258)))) + bonus 259 (HazardPattern.afterPattern 10000 p (.push 259 (.fill 258))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 259 (.fill 258)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 259 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 259 (.fill 258))) < bonus 260 p at decreasing
  rw [gammaAfter1052, at260] at decreasing
  have numeric := numeric1052 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 259 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 259 (.fill 258)))
  rw [oldBefore260, at260, literal, oldAfter1052, gammaAfter1052]
  exact numeric
theorem numeric1053 (p : Pattern) (guard : d381363 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 260 p
  rw [at260] at beforeRange
  have afterRange := bonus_range 259 (HazardPattern.afterPattern 10000 p (.push 259 (.stay 258)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 259 (.stay 258))) (HazardPattern.afterPattern 10000 p (.push 259 (.stay 258))) ∧ bonus (HazardPattern.nextHero (.push 259 (.stay 258))) (HazardPattern.afterPattern 10000 p (.push 259 (.stay 258))) ≤ 2 at afterRange
  rw [gammaAfter1053] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108286 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108286 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108286 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1053 (p : Pattern) (guard : d381363 p = 1)
    (decreasing : bonus 259 (HazardPattern.afterPattern 10000 p (.push 259 (.stay 258))) < bonus 260 p) :
    NetHack.Sokoban22Refined85.bonus 260 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 260 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 259 (.stay 258)) + NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 259 (.stay 258)))) + bonus 259 (HazardPattern.afterPattern 10000 p (.push 259 (.stay 258))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 259 (.stay 258)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 259 (.stay 258))) (HazardPattern.afterPattern 10000 p (.push 259 (.stay 258))) < bonus 260 p at decreasing
  rw [gammaAfter1053, at260] at decreasing
  have numeric := numeric1053 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 259 (.stay 258))) (HazardPattern.afterPattern 10000 p (.push 259 (.stay 258)))
  rw [oldBefore260, at260, literal, oldAfter1053, gammaAfter1053]
  exact numeric
theorem numeric1054 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 262 p
  rw [at262] at beforeRange
  have afterRange := bonus_range 240 (HazardPattern.afterPattern 10000 p (.walk 240))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 240)) (HazardPattern.afterPattern 10000 p (.walk 240)) ∧ bonus (HazardPattern.nextHero (.walk 240)) (HazardPattern.afterPattern 10000 p (.walk 240)) ≤ 2 at afterRange
  rw [gammaAfter1054] at afterRange
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
theorem local1054 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 240 (HazardPattern.afterPattern 10000 p (.walk 240)) < bonus 262 p) :
    NetHack.Sokoban22Refined85.bonus 262 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 262 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 240) + NetHack.Sokoban22Refined85.bonus 240 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 240))) + bonus 240 (HazardPattern.afterPattern 10000 p (.walk 240)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 240) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 240)) (HazardPattern.afterPattern 10000 p (.walk 240)) < bonus 262 p at decreasing
  rw [gammaAfter1054, at262] at decreasing
  have numeric := numeric1054 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 240)) (HazardPattern.afterPattern 10000 p (.walk 240))
  rw [oldBefore262, at262, literal, oldAfter1054, gammaAfter1054]
  exact numeric
theorem numeric1055 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 262 p
  rw [at262] at beforeRange
  have afterRange := bonus_range 240 (HazardPattern.afterPattern 10000 p (.push 240 (.stay 218)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 240 (.stay 218))) (HazardPattern.afterPattern 10000 p (.push 240 (.stay 218))) ∧ bonus (HazardPattern.nextHero (.push 240 (.stay 218))) (HazardPattern.afterPattern 10000 p (.push 240 (.stay 218))) ≤ 2 at afterRange
  rw [gammaAfter1055] at afterRange
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
theorem local1055 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 240 (HazardPattern.afterPattern 10000 p (.push 240 (.stay 218))) < bonus 262 p) :
    NetHack.Sokoban22Refined85.bonus 262 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 262 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 240 (.stay 218)) + NetHack.Sokoban22Refined85.bonus 240 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 240 (.stay 218)))) + bonus 240 (HazardPattern.afterPattern 10000 p (.push 240 (.stay 218))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 240 (.stay 218)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 240 (.stay 218))) (HazardPattern.afterPattern 10000 p (.push 240 (.stay 218))) < bonus 262 p at decreasing
  rw [gammaAfter1055, at262] at decreasing
  have numeric := numeric1055 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 240 (.stay 218))) (HazardPattern.afterPattern 10000 p (.push 240 (.stay 218)))
  rw [oldBefore262, at262, literal, oldAfter1055, gammaAfter1055]
  exact numeric
end NetHack.Soko22Hazard87
