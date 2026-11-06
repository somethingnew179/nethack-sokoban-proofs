import NetHack.Soko22Hazard87.Numeric002
import NetHack.Soko22Hazard87.AndIntroBlocks0036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric210 (p : Pattern) (guard : d82324 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (2 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 93 p
  rw [at93] at beforeRange
  have afterRange := bonus_range 94 (HazardPattern.afterPattern 10000 p (.push 94 (.stay 95)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 94 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 94 (.stay 95))) ∧ bonus (HazardPattern.nextHero (.push 94 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 94 (.stay 95))) ≤ 2 at afterRange
  rw [gammaAfter210] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9128 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4383 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9128 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9128 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4383 p complete
    omega
theorem local210 (p : Pattern) (guard : d82324 p = 1)
    (decreasing : bonus 94 (HazardPattern.afterPattern 10000 p (.push 94 (.stay 95))) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 94 (.stay 95)) + NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 94 (.stay 95)))) + bonus 94 (HazardPattern.afterPattern 10000 p (.push 94 (.stay 95))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 94 (.stay 95)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 94 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 94 (.stay 95))) < bonus 93 p at decreasing
  rw [gammaAfter210, at93] at decreasing
  have numeric := numeric210 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 94 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 94 (.stay 95)))
  rw [oldBefore93, at93, literal, oldAfter210, gammaAfter210]
  exact numeric
theorem numeric211 (p : Pattern) (guard : d73493 p = 1) (decreasing : d3496 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47866 p + d3496 p := by
  have beforeRange := bonus_range 93 p
  rw [at93] at beforeRange
  have afterRange := bonus_range 70 (HazardPattern.afterPattern 10000 p (.walk 70))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ∧ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ≤ 2 at afterRange
  rw [gammaAfter211] at afterRange
  have possibilities : (d0 p = 1 ∧ d3496 p = 0) ∨ (d0 p = 2 ∧ d3496 p = 0) ∨ (d0 p = 2 ∧ d3496 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro9129 p beforeEq guard
    have complete := andIntro6112 p combined afterEq
    have bound := compare4384 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro9129 p beforeEq guard
    have complete := andIntro6112 p combined afterEq
    have bound := compare4385 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1978 p pair.2
    have combined := andIntro9129 p beforeEq guard
    have complete := andIntro6113 p combined afterEq
    have bound := compare4384 p complete
    omega
theorem local211 (p : Pattern) (guard : d73493 p = 1)
    (decreasing : bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 70) + NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 70))) + bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 70) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 93 p at decreasing
  rw [gammaAfter211, at93] at decreasing
  have numeric := numeric211 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70))
  rw [oldBefore93, at93, literal, oldAfter211, gammaAfter211]
  exact numeric
theorem numeric212 (p : Pattern) (guard : d82333 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d48115 p + d0 p := by
  have beforeRange := bonus_range 93 p
  rw [at93] at beforeRange
  have afterRange := bonus_range 116 (HazardPattern.afterPattern 10000 p (.walk 116))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) ∧ bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) ≤ 2 at afterRange
  rw [gammaAfter212] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9130 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4386 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9130 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4387 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9130 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4386 p complete
    omega
theorem local212 (p : Pattern) (guard : d82333 p = 1)
    (decreasing : bonus 116 (HazardPattern.afterPattern 10000 p (.walk 116)) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 116) + NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 116))) + bonus 116 (HazardPattern.afterPattern 10000 p (.walk 116)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 116) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) < bonus 93 p at decreasing
  rw [gammaAfter212, at93] at decreasing
  have numeric := numeric212 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116))
  rw [oldBefore93, at93, literal, oldAfter212, gammaAfter212]
  exact numeric
theorem numeric213 (p : Pattern) (guard : d82334 p = 1) (decreasing : d7239 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47866 p + d7239 p := by
  have beforeRange := bonus_range 93 p
  rw [at93] at beforeRange
  have afterRange := bonus_range 114 (HazardPattern.afterPattern 10000 p (.walk 114))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) ∧ bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) ≤ 2 at afterRange
  rw [gammaAfter213] at afterRange
  have possibilities : (d0 p = 1 ∧ d7239 p = 0) ∨ (d0 p = 2 ∧ d7239 p = 0) ∨ (d0 p = 2 ∧ d7239 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro4312 p pair.2
    have combined := andIntro9131 p beforeEq guard
    have complete := andIntro9132 p combined afterEq
    have bound := compare4384 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro4312 p pair.2
    have combined := andIntro9131 p beforeEq guard
    have complete := andIntro9132 p combined afterEq
    have bound := compare4385 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro4356 p pair.2
    have combined := andIntro9131 p beforeEq guard
    have complete := andIntro9133 p combined afterEq
    have bound := compare4384 p complete
    omega
theorem local213 (p : Pattern) (guard : d82334 p = 1)
    (decreasing : bonus 114 (HazardPattern.afterPattern 10000 p (.walk 114)) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 114) + NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 114))) + bonus 114 (HazardPattern.afterPattern 10000 p (.walk 114)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 114) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) < bonus 93 p at decreasing
  rw [gammaAfter213, at93] at decreasing
  have numeric := numeric213 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114))
  rw [oldBefore93, at93, literal, oldAfter213, gammaAfter213]
  exact numeric
theorem numeric214 (p : Pattern) (guard : d82335 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d48115 p + d0 p := by
  have beforeRange := bonus_range 94 p
  rw [at94] at beforeRange
  have afterRange := bonus_range 116 (HazardPattern.afterPattern 10000 p (.walk 116))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) ∧ bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) ≤ 2 at afterRange
  rw [gammaAfter214] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9134 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4386 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9134 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4387 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9134 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4386 p complete
    omega
theorem local214 (p : Pattern) (guard : d82335 p = 1)
    (decreasing : bonus 116 (HazardPattern.afterPattern 10000 p (.walk 116)) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 116) + NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 116))) + bonus 116 (HazardPattern.afterPattern 10000 p (.walk 116)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 116) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) < bonus 94 p at decreasing
  rw [gammaAfter214, at94] at decreasing
  have numeric := numeric214 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116))
  rw [oldBefore94, at94, literal, oldAfter214, gammaAfter214]
  exact numeric
theorem numeric215 (p : Pattern) (guard : d82340 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d82346 p + d0 p := by
  have beforeRange := bonus_range 94 p
  rw [at94] at beforeRange
  have afterRange := bonus_range 116 (HazardPattern.afterPattern 10000 p (.push 116 (.stay 138)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 116 (.stay 138))) (HazardPattern.afterPattern 10000 p (.push 116 (.stay 138))) ∧ bonus (HazardPattern.nextHero (.push 116 (.stay 138))) (HazardPattern.afterPattern 10000 p (.push 116 (.stay 138))) ≤ 2 at afterRange
  rw [gammaAfter215] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9135 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4388 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9135 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4389 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9135 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4388 p complete
    omega
theorem local215 (p : Pattern) (guard : d82340 p = 1)
    (decreasing : bonus 116 (HazardPattern.afterPattern 10000 p (.push 116 (.stay 138))) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 116 (.stay 138)) + NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 116 (.stay 138)))) + bonus 116 (HazardPattern.afterPattern 10000 p (.push 116 (.stay 138))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 116 (.stay 138)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 116 (.stay 138))) (HazardPattern.afterPattern 10000 p (.push 116 (.stay 138))) < bonus 94 p at decreasing
  rw [gammaAfter215, at94] at decreasing
  have numeric := numeric215 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 116 (.stay 138))) (HazardPattern.afterPattern 10000 p (.push 116 (.stay 138)))
  rw [oldBefore94, at94, literal, oldAfter215, gammaAfter215]
  exact numeric
theorem numeric216 (p : Pattern) (guard : d82347 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 94 p
  rw [at94] at beforeRange
  have afterRange := bonus_range 95 (HazardPattern.afterPattern 10000 p (.walk 95))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) ∧ bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) ≤ 2 at afterRange
  rw [gammaAfter216] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9136 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9136 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9136 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local216 (p : Pattern) (guard : d82347 p = 1)
    (decreasing : bonus 95 (HazardPattern.afterPattern 10000 p (.walk 95)) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 95) + NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 95))) + bonus 95 (HazardPattern.afterPattern 10000 p (.walk 95)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 95) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) < bonus 94 p at decreasing
  rw [gammaAfter216, at94] at decreasing
  have numeric := numeric216 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95))
  rw [oldBefore94, at94, literal, oldAfter216, gammaAfter216]
  exact numeric
theorem numeric217 (p : Pattern) (guard : d82350 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 94 p
  rw [at94] at beforeRange
  have afterRange := bonus_range 95 (HazardPattern.afterPattern 10000 p (.push 95 (.stay 96)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 95 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 95 (.stay 96))) ∧ bonus (HazardPattern.nextHero (.push 95 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 95 (.stay 96))) ≤ 2 at afterRange
  rw [gammaAfter217] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9137 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9137 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9137 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local217 (p : Pattern) (guard : d82350 p = 1)
    (decreasing : bonus 95 (HazardPattern.afterPattern 10000 p (.push 95 (.stay 96))) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 95 (.stay 96)) + NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 95 (.stay 96)))) + bonus 95 (HazardPattern.afterPattern 10000 p (.push 95 (.stay 96))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 95 (.stay 96)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 95 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 95 (.stay 96))) < bonus 94 p at decreasing
  rw [gammaAfter217, at94] at decreasing
  have numeric := numeric217 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 95 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 95 (.stay 96)))
  rw [oldBefore94, at94, literal, oldAfter217, gammaAfter217]
  exact numeric
theorem numeric218 (p : Pattern) (guard : d82321 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 94 p
  rw [at94] at beforeRange
  have afterRange := bonus_range 93 (HazardPattern.afterPattern 10000 p (.walk 93))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) ∧ bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) ≤ 2 at afterRange
  rw [gammaAfter218] at afterRange
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
theorem local218 (p : Pattern) (guard : d82321 p = 1)
    (decreasing : bonus 93 (HazardPattern.afterPattern 10000 p (.walk 93)) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 93) + NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 93))) + bonus 93 (HazardPattern.afterPattern 10000 p (.walk 93)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 93) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) < bonus 94 p at decreasing
  rw [gammaAfter218, at94] at decreasing
  have numeric := numeric218 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93))
  rw [oldBefore94, at94, literal, oldAfter218, gammaAfter218]
  exact numeric
theorem numeric219 (p : Pattern) (guard : d74047 p = 1) (decreasing : d3842 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d3842 p := by
  have beforeRange := bonus_range 94 p
  rw [at94] at beforeRange
  have afterRange := bonus_range 73 (HazardPattern.afterPattern 10000 p (.walk 73))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ∧ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ≤ 2 at afterRange
  rw [gammaAfter219] at afterRange
  have possibilities : (d0 p = 1 ∧ d3842 p = 0) ∨ (d0 p = 2 ∧ d3842 p = 0) ∨ (d0 p = 2 ∧ d3842 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro6554 p beforeEq guard
    have complete := andIntro2877 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro6554 p beforeEq guard
    have complete := andIntro2877 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2342 p pair.2
    have combined := andIntro6554 p beforeEq guard
    have complete := andIntro2879 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local219 (p : Pattern) (guard : d74047 p = 1)
    (decreasing : bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 73) + NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 73))) + bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 73) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 94 p at decreasing
  rw [gammaAfter219, at94] at decreasing
  have numeric := numeric219 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73))
  rw [oldBefore94, at94, literal, oldAfter219, gammaAfter219]
  exact numeric
theorem numeric220 (p : Pattern) (guard : d74039 p = 1) (decreasing : d3673 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d48087 p + d3673 p := by
  have beforeRange := bonus_range 94 p
  rw [at94] at beforeRange
  have afterRange := bonus_range 71 (HazardPattern.afterPattern 10000 p (.walk 71))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) ∧ bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) ≤ 2 at afterRange
  rw [gammaAfter220] at afterRange
  have possibilities : (d0 p = 1 ∧ d3673 p = 0) ∨ (d0 p = 2 ∧ d3673 p = 0) ∨ (d0 p = 2 ∧ d3673 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro2078 p pair.2
    have combined := andIntro9138 p beforeEq guard
    have complete := andIntro2923 p combined afterEq
    have bound := compare2476 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2078 p pair.2
    have combined := andIntro9138 p beforeEq guard
    have complete := andIntro2923 p combined afterEq
    have bound := compare2477 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2106 p pair.2
    have combined := andIntro9138 p beforeEq guard
    have complete := andIntro2924 p combined afterEq
    have bound := compare2476 p complete
    omega
theorem local220 (p : Pattern) (guard : d74039 p = 1)
    (decreasing : bonus 71 (HazardPattern.afterPattern 10000 p (.walk 71)) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 71) + NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 71))) + bonus 71 (HazardPattern.afterPattern 10000 p (.walk 71)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 71) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) < bonus 94 p at decreasing
  rw [gammaAfter220, at94] at decreasing
  have numeric := numeric220 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71))
  rw [oldBefore94, at94, literal, oldAfter220, gammaAfter220]
  exact numeric
theorem numeric221 (p : Pattern) (guard : d82355 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d48097 p + d0 p := by
  have beforeRange := bonus_range 94 p
  rw [at94] at beforeRange
  have afterRange := bonus_range 115 (HazardPattern.afterPattern 10000 p (.walk 115))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) ∧ bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) ≤ 2 at afterRange
  rw [gammaAfter221] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9139 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4381 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9139 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4382 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9139 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4381 p complete
    omega
theorem local221 (p : Pattern) (guard : d82355 p = 1)
    (decreasing : bonus 115 (HazardPattern.afterPattern 10000 p (.walk 115)) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 115) + NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 115))) + bonus 115 (HazardPattern.afterPattern 10000 p (.walk 115)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 115) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) < bonus 94 p at decreasing
  rw [gammaAfter221, at94] at decreasing
  have numeric := numeric221 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115))
  rw [oldBefore94, at94, literal, oldAfter221, gammaAfter221]
  exact numeric
theorem numeric222 (p : Pattern) (guard : d74040 p = 1) (decreasing : d3842 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d3842 p := by
  have beforeRange := bonus_range 95 p
  rw [at95] at beforeRange
  have afterRange := bonus_range 73 (HazardPattern.afterPattern 10000 p (.walk 73))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ∧ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ≤ 2 at afterRange
  rw [gammaAfter222] at afterRange
  have possibilities : (d0 p = 1 ∧ d3842 p = 0) ∨ (d0 p = 2 ∧ d3842 p = 0) ∨ (d0 p = 2 ∧ d3842 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro6411 p beforeEq guard
    have complete := andIntro2877 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro6411 p beforeEq guard
    have complete := andIntro2877 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2342 p pair.2
    have combined := andIntro6411 p beforeEq guard
    have complete := andIntro2879 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local222 (p : Pattern) (guard : d74040 p = 1)
    (decreasing : bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 73) + NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 73))) + bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 73) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 95 p at decreasing
  rw [gammaAfter222, at95] at decreasing
  have numeric := numeric222 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73))
  rw [oldBefore95, at95, literal, oldAfter222, gammaAfter222]
  exact numeric
theorem numeric223 (p : Pattern) (guard : d65090 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 95 p
  rw [at95] at beforeRange
  have afterRange := bonus_range 73 (HazardPattern.afterPattern 10000 p (.push 73 (.stay 51)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 73 (.stay 51))) (HazardPattern.afterPattern 10000 p (.push 73 (.stay 51))) ∧ bonus (HazardPattern.nextHero (.push 73 (.stay 51))) (HazardPattern.afterPattern 10000 p (.push 73 (.stay 51))) ≤ 2 at afterRange
  rw [gammaAfter223] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9140 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9140 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9140 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local223 (p : Pattern) (guard : d65090 p = 1)
    (decreasing : bonus 73 (HazardPattern.afterPattern 10000 p (.push 73 (.stay 51))) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 73 (.stay 51)) + NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 73 (.stay 51)))) + bonus 73 (HazardPattern.afterPattern 10000 p (.push 73 (.stay 51))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 73 (.stay 51)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 73 (.stay 51))) (HazardPattern.afterPattern 10000 p (.push 73 (.stay 51))) < bonus 95 p at decreasing
  rw [gammaAfter223, at95] at decreasing
  have numeric := numeric223 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 73 (.stay 51))) (HazardPattern.afterPattern 10000 p (.push 73 (.stay 51)))
  rw [oldBefore95, at95, literal, oldAfter223, gammaAfter223]
  exact numeric
theorem numeric224 (p : Pattern) (guard : d74044 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 95 p
  rw [at95] at beforeRange
  have afterRange := bonus_range 96 (HazardPattern.afterPattern 10000 p (.walk 96))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) ∧ bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) ≤ 2 at afterRange
  rw [gammaAfter224] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9141 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9141 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9141 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local224 (p : Pattern) (guard : d74044 p = 1)
    (decreasing : bonus 96 (HazardPattern.afterPattern 10000 p (.walk 96)) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 96) + NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 96))) + bonus 96 (HazardPattern.afterPattern 10000 p (.walk 96)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 96) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) < bonus 95 p at decreasing
  rw [gammaAfter224, at95] at decreasing
  have numeric := numeric224 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96))
  rw [oldBefore95, at95, literal, oldAfter224, gammaAfter224]
  exact numeric
theorem numeric225 (p : Pattern) (guard : d82357 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 95 p
  rw [at95] at beforeRange
  have afterRange := bonus_range 96 (HazardPattern.afterPattern 10000 p (.push 96 (.stay 97)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 96 (.stay 97))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 97))) ∧ bonus (HazardPattern.nextHero (.push 96 (.stay 97))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 97))) ≤ 2 at afterRange
  rw [gammaAfter225] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9142 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9142 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9142 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local225 (p : Pattern) (guard : d82357 p = 1)
    (decreasing : bonus 96 (HazardPattern.afterPattern 10000 p (.push 96 (.stay 97))) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 96 (.stay 97)) + NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 96 (.stay 97)))) + bonus 96 (HazardPattern.afterPattern 10000 p (.push 96 (.stay 97))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 96 (.stay 97)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 96 (.stay 97))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 97))) < bonus 95 p at decreasing
  rw [gammaAfter225, at95] at decreasing
  have numeric := numeric225 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 96 (.stay 97))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 97)))
  rw [oldBefore95, at95, literal, oldAfter225, gammaAfter225]
  exact numeric
theorem numeric226 (p : Pattern) (guard : d82347 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 95 p
  rw [at95] at beforeRange
  have afterRange := bonus_range 94 (HazardPattern.afterPattern 10000 p (.walk 94))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) ∧ bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) ≤ 2 at afterRange
  rw [gammaAfter226] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9136 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9136 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9136 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local226 (p : Pattern) (guard : d82347 p = 1)
    (decreasing : bonus 94 (HazardPattern.afterPattern 10000 p (.walk 94)) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 94) + NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 94))) + bonus 94 (HazardPattern.afterPattern 10000 p (.walk 94)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 94) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) < bonus 95 p at decreasing
  rw [gammaAfter226, at95] at decreasing
  have numeric := numeric226 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94))
  rw [oldBefore95, at95, literal, oldAfter226, gammaAfter226]
  exact numeric
theorem numeric227 (p : Pattern) (guard : d82324 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 95 p
  rw [at95] at beforeRange
  have afterRange := bonus_range 94 (HazardPattern.afterPattern 10000 p (.push 94 (.stay 93)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 94 (.stay 93))) (HazardPattern.afterPattern 10000 p (.push 94 (.stay 93))) ∧ bonus (HazardPattern.nextHero (.push 94 (.stay 93))) (HazardPattern.afterPattern 10000 p (.push 94 (.stay 93))) ≤ 2 at afterRange
  rw [gammaAfter227] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9128 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9128 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9128 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local227 (p : Pattern) (guard : d82324 p = 1)
    (decreasing : bonus 94 (HazardPattern.afterPattern 10000 p (.push 94 (.stay 93))) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 94 (.stay 93)) + NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 94 (.stay 93)))) + bonus 94 (HazardPattern.afterPattern 10000 p (.push 94 (.stay 93))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 94 (.stay 93)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 94 (.stay 93))) (HazardPattern.afterPattern 10000 p (.push 94 (.stay 93))) < bonus 95 p at decreasing
  rw [gammaAfter227, at95] at decreasing
  have numeric := numeric227 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 94 (.stay 93))) (HazardPattern.afterPattern 10000 p (.push 94 (.stay 93)))
  rw [oldBefore95, at95, literal, oldAfter227, gammaAfter227]
  exact numeric
theorem numeric228 (p : Pattern) (guard : d74062 p = 1) (decreasing : d4025 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d4025 p := by
  have beforeRange := bonus_range 95 p
  rw [at95] at beforeRange
  have afterRange := bonus_range 74 (HazardPattern.afterPattern 10000 p (.walk 74))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) ∧ bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) ≤ 2 at afterRange
  rw [gammaAfter228] at afterRange
  have possibilities : (d0 p = 1 ∧ d4025 p = 0) ∨ (d0 p = 2 ∧ d4025 p = 0) ∨ (d0 p = 2 ∧ d4025 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro2480 p pair.2
    have combined := andIntro6779 p beforeEq guard
    have complete := andIntro3414 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2480 p pair.2
    have combined := andIntro6779 p beforeEq guard
    have complete := andIntro3414 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2481 p pair.2
    have combined := andIntro6779 p beforeEq guard
    have complete := andIntro3415 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local228 (p : Pattern) (guard : d74062 p = 1)
    (decreasing : bonus 74 (HazardPattern.afterPattern 10000 p (.walk 74)) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 74) + NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 74))) + bonus 74 (HazardPattern.afterPattern 10000 p (.walk 74)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 74) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) < bonus 95 p at decreasing
  rw [gammaAfter228, at95] at decreasing
  have numeric := numeric228 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74))
  rw [oldBefore95, at95, literal, oldAfter228, gammaAfter228]
  exact numeric
theorem numeric229 (p : Pattern) (guard : d82360 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 95 p
  rw [at95] at beforeRange
  have afterRange := bonus_range 118 (HazardPattern.afterPattern 10000 p (.walk 118))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) ∧ bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) ≤ 2 at afterRange
  rw [gammaAfter229] at afterRange
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
theorem local229 (p : Pattern) (guard : d82360 p = 1)
    (decreasing : bonus 118 (HazardPattern.afterPattern 10000 p (.walk 118)) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 118) + NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 118))) + bonus 118 (HazardPattern.afterPattern 10000 p (.walk 118)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 118) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) < bonus 95 p at decreasing
  rw [gammaAfter229, at95] at decreasing
  have numeric := numeric229 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118))
  rw [oldBefore95, at95, literal, oldAfter229, gammaAfter229]
  exact numeric
theorem numeric230 (p : Pattern) (guard : d82362 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d48115 p + d0 p := by
  have beforeRange := bonus_range 95 p
  rw [at95] at beforeRange
  have afterRange := bonus_range 116 (HazardPattern.afterPattern 10000 p (.walk 116))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) ∧ bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) ≤ 2 at afterRange
  rw [gammaAfter230] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9144 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4386 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9144 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4387 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9144 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4386 p complete
    omega
theorem local230 (p : Pattern) (guard : d82362 p = 1)
    (decreasing : bonus 116 (HazardPattern.afterPattern 10000 p (.walk 116)) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 116) + NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 116))) + bonus 116 (HazardPattern.afterPattern 10000 p (.walk 116)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 116) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) < bonus 95 p at decreasing
  rw [gammaAfter230, at95] at decreasing
  have numeric := numeric230 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116))
  rw [oldBefore95, at95, literal, oldAfter230, gammaAfter230]
  exact numeric
theorem numeric231 (p : Pattern) (guard : d74048 p = 1) (decreasing : d4025 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d4025 p := by
  have beforeRange := bonus_range 96 p
  rw [at96] at beforeRange
  have afterRange := bonus_range 74 (HazardPattern.afterPattern 10000 p (.walk 74))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) ∧ bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) ≤ 2 at afterRange
  rw [gammaAfter231] at afterRange
  have possibilities : (d0 p = 1 ∧ d4025 p = 0) ∨ (d0 p = 2 ∧ d4025 p = 0) ∨ (d0 p = 2 ∧ d4025 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro2480 p pair.2
    have combined := andIntro6654 p beforeEq guard
    have complete := andIntro3414 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2480 p pair.2
    have combined := andIntro6654 p beforeEq guard
    have complete := andIntro3414 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2481 p pair.2
    have combined := andIntro6654 p beforeEq guard
    have complete := andIntro3415 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local231 (p : Pattern) (guard : d74048 p = 1)
    (decreasing : bonus 74 (HazardPattern.afterPattern 10000 p (.walk 74)) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 74) + NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 74))) + bonus 74 (HazardPattern.afterPattern 10000 p (.walk 74)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 74) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) < bonus 96 p at decreasing
  rw [gammaAfter231, at96] at decreasing
  have numeric := numeric231 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74))
  rw [oldBefore96, at96, literal, oldAfter231, gammaAfter231]
  exact numeric
theorem numeric232 (p : Pattern) (guard : d66280 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 96 p
  rw [at96] at beforeRange
  have afterRange := bonus_range 74 (HazardPattern.afterPattern 10000 p (.push 74 (.stay 52)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 74 (.stay 52))) (HazardPattern.afterPattern 10000 p (.push 74 (.stay 52))) ∧ bonus (HazardPattern.nextHero (.push 74 (.stay 52))) (HazardPattern.afterPattern 10000 p (.push 74 (.stay 52))) ≤ 2 at afterRange
  rw [gammaAfter232] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9145 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9145 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9145 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local232 (p : Pattern) (guard : d66280 p = 1)
    (decreasing : bonus 74 (HazardPattern.afterPattern 10000 p (.push 74 (.stay 52))) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 74 (.stay 52)) + NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 74 (.stay 52)))) + bonus 74 (HazardPattern.afterPattern 10000 p (.push 74 (.stay 52))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 74 (.stay 52)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 74 (.stay 52))) (HazardPattern.afterPattern 10000 p (.push 74 (.stay 52))) < bonus 96 p at decreasing
  rw [gammaAfter232, at96] at decreasing
  have numeric := numeric232 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 74 (.stay 52))) (HazardPattern.afterPattern 10000 p (.push 74 (.stay 52)))
  rw [oldBefore96, at96, literal, oldAfter232, gammaAfter232]
  exact numeric
theorem numeric233 (p : Pattern) (guard : d82363 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 96 p
  rw [at96] at beforeRange
  have afterRange := bonus_range 118 (HazardPattern.afterPattern 10000 p (.walk 118))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) ∧ bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) ≤ 2 at afterRange
  rw [gammaAfter233] at afterRange
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
theorem local233 (p : Pattern) (guard : d82363 p = 1)
    (decreasing : bonus 118 (HazardPattern.afterPattern 10000 p (.walk 118)) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 118) + NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 118))) + bonus 118 (HazardPattern.afterPattern 10000 p (.walk 118)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 118) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) < bonus 96 p at decreasing
  rw [gammaAfter233, at96] at decreasing
  have numeric := numeric233 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118))
  rw [oldBefore96, at96, literal, oldAfter233, gammaAfter233]
  exact numeric
theorem numeric234 (p : Pattern) (guard : d82364 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 96 p
  rw [at96] at beforeRange
  have afterRange := bonus_range 97 (HazardPattern.afterPattern 10000 p (.walk 97))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ∧ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ≤ 2 at afterRange
  rw [gammaAfter234] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9147 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9147 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9147 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local234 (p : Pattern) (guard : d82364 p = 1)
    (decreasing : bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 97) + NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 97))) + bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 97) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 96 p at decreasing
  rw [gammaAfter234, at96] at decreasing
  have numeric := numeric234 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97))
  rw [oldBefore96, at96, literal, oldAfter234, gammaAfter234]
  exact numeric
theorem numeric235 (p : Pattern) (guard : d82367 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 96 p
  rw [at96] at beforeRange
  have afterRange := bonus_range 97 (HazardPattern.afterPattern 10000 p (.push 97 (.stay 98)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 97 (.stay 98))) (HazardPattern.afterPattern 10000 p (.push 97 (.stay 98))) ∧ bonus (HazardPattern.nextHero (.push 97 (.stay 98))) (HazardPattern.afterPattern 10000 p (.push 97 (.stay 98))) ≤ 2 at afterRange
  rw [gammaAfter235] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9148 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9148 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9148 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local235 (p : Pattern) (guard : d82367 p = 1)
    (decreasing : bonus 97 (HazardPattern.afterPattern 10000 p (.push 97 (.stay 98))) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 97 (.stay 98)) + NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 97 (.stay 98)))) + bonus 97 (HazardPattern.afterPattern 10000 p (.push 97 (.stay 98))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 97 (.stay 98)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 97 (.stay 98))) (HazardPattern.afterPattern 10000 p (.push 97 (.stay 98))) < bonus 96 p at decreasing
  rw [gammaAfter235, at96] at decreasing
  have numeric := numeric235 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 97 (.stay 98))) (HazardPattern.afterPattern 10000 p (.push 97 (.stay 98)))
  rw [oldBefore96, at96, literal, oldAfter235, gammaAfter235]
  exact numeric
theorem numeric236 (p : Pattern) (guard : d74044 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 96 p
  rw [at96] at beforeRange
  have afterRange := bonus_range 95 (HazardPattern.afterPattern 10000 p (.walk 95))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) ∧ bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) ≤ 2 at afterRange
  rw [gammaAfter236] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9141 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9141 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9141 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local236 (p : Pattern) (guard : d74044 p = 1)
    (decreasing : bonus 95 (HazardPattern.afterPattern 10000 p (.walk 95)) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 95) + NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 95))) + bonus 95 (HazardPattern.afterPattern 10000 p (.walk 95)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 95) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) < bonus 96 p at decreasing
  rw [gammaAfter236, at96] at decreasing
  have numeric := numeric236 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95))
  rw [oldBefore96, at96, literal, oldAfter236, gammaAfter236]
  exact numeric
theorem numeric237 (p : Pattern) (guard : d82350 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 96 p
  rw [at96] at beforeRange
  have afterRange := bonus_range 95 (HazardPattern.afterPattern 10000 p (.push 95 (.stay 94)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 95 (.stay 94))) (HazardPattern.afterPattern 10000 p (.push 95 (.stay 94))) ∧ bonus (HazardPattern.nextHero (.push 95 (.stay 94))) (HazardPattern.afterPattern 10000 p (.push 95 (.stay 94))) ≤ 2 at afterRange
  rw [gammaAfter237] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9137 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9137 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9137 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local237 (p : Pattern) (guard : d82350 p = 1)
    (decreasing : bonus 95 (HazardPattern.afterPattern 10000 p (.push 95 (.stay 94))) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 95 (.stay 94)) + NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 95 (.stay 94)))) + bonus 95 (HazardPattern.afterPattern 10000 p (.push 95 (.stay 94))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 95 (.stay 94)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 95 (.stay 94))) (HazardPattern.afterPattern 10000 p (.push 95 (.stay 94))) < bonus 96 p at decreasing
  rw [gammaAfter237, at96] at decreasing
  have numeric := numeric237 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 95 (.stay 94))) (HazardPattern.afterPattern 10000 p (.push 95 (.stay 94)))
  rw [oldBefore96, at96, literal, oldAfter237, gammaAfter237]
  exact numeric
theorem numeric238 (p : Pattern) (guard : d74046 p = 1) (decreasing : d3842 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d3842 p := by
  have beforeRange := bonus_range 96 p
  rw [at96] at beforeRange
  have afterRange := bonus_range 73 (HazardPattern.afterPattern 10000 p (.walk 73))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ∧ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ≤ 2 at afterRange
  rw [gammaAfter238] at afterRange
  have possibilities : (d0 p = 1 ∧ d3842 p = 0) ∨ (d0 p = 2 ∧ d3842 p = 0) ∨ (d0 p = 2 ∧ d3842 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro6551 p beforeEq guard
    have complete := andIntro2877 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro6551 p beforeEq guard
    have complete := andIntro2877 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2342 p pair.2
    have combined := andIntro6551 p beforeEq guard
    have complete := andIntro2879 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local238 (p : Pattern) (guard : d74046 p = 1)
    (decreasing : bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 73) + NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 73))) + bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 73) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 96 p at decreasing
  rw [gammaAfter238, at96] at decreasing
  have numeric := numeric238 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73))
  rw [oldBefore96, at96, literal, oldAfter238, gammaAfter238]
  exact numeric
theorem numeric239 (p : Pattern) (guard : d82375 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 96 p
  rw [at96] at beforeRange
  have afterRange := bonus_range 119 (HazardPattern.afterPattern 10000 p (.walk 119))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) ∧ bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) ≤ 2 at afterRange
  rw [gammaAfter239] at afterRange
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
theorem local239 (p : Pattern) (guard : d82375 p = 1)
    (decreasing : bonus 119 (HazardPattern.afterPattern 10000 p (.walk 119)) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 119) + NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 119))) + bonus 119 (HazardPattern.afterPattern 10000 p (.walk 119)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 119) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) < bonus 96 p at decreasing
  rw [gammaAfter239, at96] at decreasing
  have numeric := numeric239 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119))
  rw [oldBefore96, at96, literal, oldAfter239, gammaAfter239]
  exact numeric
theorem numeric240 (p : Pattern) (guard : d82376 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 97 p
  rw [at97] at beforeRange
  have afterRange := bonus_range 119 (HazardPattern.afterPattern 10000 p (.walk 119))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) ∧ bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) ≤ 2 at afterRange
  rw [gammaAfter240] at afterRange
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
theorem local240 (p : Pattern) (guard : d82376 p = 1)
    (decreasing : bonus 119 (HazardPattern.afterPattern 10000 p (.walk 119)) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 119) + NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 119))) + bonus 119 (HazardPattern.afterPattern 10000 p (.walk 119)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 119) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) < bonus 97 p at decreasing
  rw [gammaAfter240, at97] at decreasing
  have numeric := numeric240 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119))
  rw [oldBefore97, at97, literal, oldAfter240, gammaAfter240]
  exact numeric
theorem numeric241 (p : Pattern) (guard : d82381 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d82402 p + d0 p := by
  have beforeRange := bonus_range 97 p
  rw [at97] at beforeRange
  have afterRange := bonus_range 119 (HazardPattern.afterPattern 10000 p (.push 119 (.stay 141)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 119 (.stay 141))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 141))) ∧ bonus (HazardPattern.nextHero (.push 119 (.stay 141))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 141))) ≤ 2 at afterRange
  rw [gammaAfter241] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9151 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4390 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9151 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4391 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9151 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4390 p complete
    omega
theorem local241 (p : Pattern) (guard : d82381 p = 1)
    (decreasing : bonus 119 (HazardPattern.afterPattern 10000 p (.push 119 (.stay 141))) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 119 (.stay 141)) + NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 119 (.stay 141)))) + bonus 119 (HazardPattern.afterPattern 10000 p (.push 119 (.stay 141))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 119 (.stay 141)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 119 (.stay 141))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 141))) < bonus 97 p at decreasing
  rw [gammaAfter241, at97] at decreasing
  have numeric := numeric241 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 119 (.stay 141))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 141)))
  rw [oldBefore97, at97, literal, oldAfter241, gammaAfter241]
  exact numeric
theorem numeric242 (p : Pattern) (guard : d74073 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 97 p
  rw [at97] at beforeRange
  have afterRange := bonus_range 98 (HazardPattern.afterPattern 10000 p (.walk 98))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) ∧ bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) ≤ 2 at afterRange
  rw [gammaAfter242] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9152 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9152 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9152 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local242 (p : Pattern) (guard : d74073 p = 1)
    (decreasing : bonus 98 (HazardPattern.afterPattern 10000 p (.walk 98)) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 98) + NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 98))) + bonus 98 (HazardPattern.afterPattern 10000 p (.walk 98)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 98) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) < bonus 97 p at decreasing
  rw [gammaAfter242, at97] at decreasing
  have numeric := numeric242 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98))
  rw [oldBefore97, at97, literal, oldAfter242, gammaAfter242]
  exact numeric
theorem numeric243 (p : Pattern) (guard : d82364 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 97 p
  rw [at97] at beforeRange
  have afterRange := bonus_range 96 (HazardPattern.afterPattern 10000 p (.walk 96))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) ∧ bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) ≤ 2 at afterRange
  rw [gammaAfter243] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9147 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9147 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9147 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local243 (p : Pattern) (guard : d82364 p = 1)
    (decreasing : bonus 96 (HazardPattern.afterPattern 10000 p (.walk 96)) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 96) + NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 96))) + bonus 96 (HazardPattern.afterPattern 10000 p (.walk 96)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 96) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) < bonus 97 p at decreasing
  rw [gammaAfter243, at97] at decreasing
  have numeric := numeric243 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96))
  rw [oldBefore97, at97, literal, oldAfter243, gammaAfter243]
  exact numeric
theorem numeric244 (p : Pattern) (guard : d82357 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 97 p
  rw [at97] at beforeRange
  have afterRange := bonus_range 96 (HazardPattern.afterPattern 10000 p (.push 96 (.stay 95)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 96 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 95))) ∧ bonus (HazardPattern.nextHero (.push 96 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 95))) ≤ 2 at afterRange
  rw [gammaAfter244] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9142 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9142 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9142 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local244 (p : Pattern) (guard : d82357 p = 1)
    (decreasing : bonus 96 (HazardPattern.afterPattern 10000 p (.push 96 (.stay 95))) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 96 (.stay 95)) + NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 96 (.stay 95)))) + bonus 96 (HazardPattern.afterPattern 10000 p (.push 96 (.stay 95))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 96 (.stay 95)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 96 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 95))) < bonus 97 p at decreasing
  rw [gammaAfter244, at97] at decreasing
  have numeric := numeric244 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 96 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 95)))
  rw [oldBefore97, at97, literal, oldAfter244, gammaAfter244]
  exact numeric
theorem numeric245 (p : Pattern) (guard : d74074 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 97 p
  rw [at97] at beforeRange
  have afterRange := bonus_range 76 (HazardPattern.afterPattern 10000 p (.walk 76))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 76)) (HazardPattern.afterPattern 10000 p (.walk 76)) ∧ bonus (HazardPattern.nextHero (.walk 76)) (HazardPattern.afterPattern 10000 p (.walk 76)) ≤ 2 at afterRange
  rw [gammaAfter245] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6782 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6782 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6782 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local245 (p : Pattern) (guard : d74074 p = 1)
    (decreasing : bonus 76 (HazardPattern.afterPattern 10000 p (.walk 76)) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 76) + NetHack.Sokoban22Refined85.bonus 76 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 76))) + bonus 76 (HazardPattern.afterPattern 10000 p (.walk 76)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 76) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 76)) (HazardPattern.afterPattern 10000 p (.walk 76)) < bonus 97 p at decreasing
  rw [gammaAfter245, at97] at decreasing
  have numeric := numeric245 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 76)) (HazardPattern.afterPattern 10000 p (.walk 76))
  rw [oldBefore97, at97, literal, oldAfter245, gammaAfter245]
  exact numeric
theorem numeric246 (p : Pattern) (guard : d74056 p = 1) (decreasing : d4025 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d4025 p := by
  have beforeRange := bonus_range 97 p
  rw [at97] at beforeRange
  have afterRange := bonus_range 74 (HazardPattern.afterPattern 10000 p (.walk 74))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) ∧ bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) ≤ 2 at afterRange
  rw [gammaAfter246] at afterRange
  have possibilities : (d0 p = 1 ∧ d4025 p = 0) ∨ (d0 p = 2 ∧ d4025 p = 0) ∨ (d0 p = 2 ∧ d4025 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro2480 p pair.2
    have combined := andIntro6719 p beforeEq guard
    have complete := andIntro3414 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2480 p pair.2
    have combined := andIntro6719 p beforeEq guard
    have complete := andIntro3414 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro2481 p pair.2
    have combined := andIntro6719 p beforeEq guard
    have complete := andIntro3415 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local246 (p : Pattern) (guard : d74056 p = 1)
    (decreasing : bonus 74 (HazardPattern.afterPattern 10000 p (.walk 74)) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 74) + NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 74))) + bonus 74 (HazardPattern.afterPattern 10000 p (.walk 74)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 74) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) < bonus 97 p at decreasing
  rw [gammaAfter246, at97] at decreasing
  have numeric := numeric246 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74))
  rw [oldBefore97, at97, literal, oldAfter246, gammaAfter246]
  exact numeric
theorem numeric247 (p : Pattern) (guard : d82409 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 97 p
  rw [at97] at beforeRange
  have afterRange := bonus_range 120 (HazardPattern.afterPattern 10000 p (.walk 120))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) ∧ bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) ≤ 2 at afterRange
  rw [gammaAfter247] at afterRange
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
theorem local247 (p : Pattern) (guard : d82409 p = 1)
    (decreasing : bonus 120 (HazardPattern.afterPattern 10000 p (.walk 120)) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 120) + NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 120))) + bonus 120 (HazardPattern.afterPattern 10000 p (.walk 120)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 120) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) < bonus 97 p at decreasing
  rw [gammaAfter247, at97] at decreasing
  have numeric := numeric247 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120))
  rw [oldBefore97, at97, literal, oldAfter247, gammaAfter247]
  exact numeric
theorem numeric248 (p : Pattern) (guard : d82414 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 97 p
  rw [at97] at beforeRange
  have afterRange := bonus_range 118 (HazardPattern.afterPattern 10000 p (.walk 118))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) ∧ bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) ≤ 2 at afterRange
  rw [gammaAfter248] at afterRange
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
theorem local248 (p : Pattern) (guard : d82414 p = 1)
    (decreasing : bonus 118 (HazardPattern.afterPattern 10000 p (.walk 118)) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 118) + NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 118))) + bonus 118 (HazardPattern.afterPattern 10000 p (.walk 118)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 118) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) < bonus 97 p at decreasing
  rw [gammaAfter248, at97] at decreasing
  have numeric := numeric248 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118))
  rw [oldBefore97, at97, literal, oldAfter248, gammaAfter248]
  exact numeric
theorem numeric249 (p : Pattern) (guard : d74067 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 98 p
  rw [at98] at beforeRange
  have afterRange := bonus_range 76 (HazardPattern.afterPattern 10000 p (.walk 76))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 76)) (HazardPattern.afterPattern 10000 p (.walk 76)) ∧ bonus (HazardPattern.nextHero (.walk 76)) (HazardPattern.afterPattern 10000 p (.walk 76)) ≤ 2 at afterRange
  rw [gammaAfter249] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6780 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6780 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6780 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local249 (p : Pattern) (guard : d74067 p = 1)
    (decreasing : bonus 76 (HazardPattern.afterPattern 10000 p (.walk 76)) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 76) + NetHack.Sokoban22Refined85.bonus 76 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 76))) + bonus 76 (HazardPattern.afterPattern 10000 p (.walk 76)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 76) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 76)) (HazardPattern.afterPattern 10000 p (.walk 76)) < bonus 98 p at decreasing
  rw [gammaAfter249, at98] at decreasing
  have numeric := numeric249 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 76)) (HazardPattern.afterPattern 10000 p (.walk 76))
  rw [oldBefore98, at98, literal, oldAfter249, gammaAfter249]
  exact numeric
theorem numeric250 (p : Pattern) (guard : d82415 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 98 p
  rw [at98] at beforeRange
  have afterRange := bonus_range 120 (HazardPattern.afterPattern 10000 p (.walk 120))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) ∧ bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) ≤ 2 at afterRange
  rw [gammaAfter250] at afterRange
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
theorem local250 (p : Pattern) (guard : d82415 p = 1)
    (decreasing : bonus 120 (HazardPattern.afterPattern 10000 p (.walk 120)) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 120) + NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 120))) + bonus 120 (HazardPattern.afterPattern 10000 p (.walk 120)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 120) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) < bonus 98 p at decreasing
  rw [gammaAfter250, at98] at decreasing
  have numeric := numeric250 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120))
  rw [oldBefore98, at98, literal, oldAfter250, gammaAfter250]
  exact numeric
theorem numeric251 (p : Pattern) (guard : d74073 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 98 p
  rw [at98] at beforeRange
  have afterRange := bonus_range 97 (HazardPattern.afterPattern 10000 p (.walk 97))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ∧ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ≤ 2 at afterRange
  rw [gammaAfter251] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9152 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9152 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9152 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local251 (p : Pattern) (guard : d74073 p = 1)
    (decreasing : bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 97) + NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 97))) + bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 97) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 98 p at decreasing
  rw [gammaAfter251, at98] at decreasing
  have numeric := numeric251 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97))
  rw [oldBefore98, at98, literal, oldAfter251, gammaAfter251]
  exact numeric
theorem numeric252 (p : Pattern) (guard : d82367 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 98 p
  rw [at98] at beforeRange
  have afterRange := bonus_range 97 (HazardPattern.afterPattern 10000 p (.push 97 (.stay 96)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 97 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 97 (.stay 96))) ∧ bonus (HazardPattern.nextHero (.push 97 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 97 (.stay 96))) ≤ 2 at afterRange
  rw [gammaAfter252] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9148 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro9148 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro9148 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local252 (p : Pattern) (guard : d82367 p = 1)
    (decreasing : bonus 97 (HazardPattern.afterPattern 10000 p (.push 97 (.stay 96))) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 97 (.stay 96)) + NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 97 (.stay 96)))) + bonus 97 (HazardPattern.afterPattern 10000 p (.push 97 (.stay 96))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 97 (.stay 96)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 97 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 97 (.stay 96))) < bonus 98 p at decreasing
  rw [gammaAfter252, at98] at decreasing
  have numeric := numeric252 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 97 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 97 (.stay 96)))
  rw [oldBefore98, at98, literal, oldAfter252, gammaAfter252]
  exact numeric
theorem numeric253 (p : Pattern) (guard : d82422 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 98 p
  rw [at98] at beforeRange
  have afterRange := bonus_range 119 (HazardPattern.afterPattern 10000 p (.walk 119))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) ∧ bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) ≤ 2 at afterRange
  rw [gammaAfter253] at afterRange
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
theorem local253 (p : Pattern) (guard : d82422 p = 1)
    (decreasing : bonus 119 (HazardPattern.afterPattern 10000 p (.walk 119)) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 119) + NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 119))) + bonus 119 (HazardPattern.afterPattern 10000 p (.walk 119)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 119) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) < bonus 98 p at decreasing
  rw [gammaAfter253, at98] at decreasing
  have numeric := numeric253 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119))
  rw [oldBefore98, at98, literal, oldAfter253, gammaAfter253]
  exact numeric
theorem numeric254 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 100 p
  rw [at100] at beforeRange
  have afterRange := bonus_range 78 (HazardPattern.afterPattern 10000 p (.walk 78))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78)) ∧ bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78)) ≤ 2 at afterRange
  rw [gammaAfter254] at afterRange
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
theorem local254 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 78 (HazardPattern.afterPattern 10000 p (.walk 78)) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 78) + NetHack.Sokoban22Refined85.bonus 78 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 78))) + bonus 78 (HazardPattern.afterPattern 10000 p (.walk 78)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 78) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78)) < bonus 100 p at decreasing
  rw [gammaAfter254, at100] at decreasing
  have numeric := numeric254 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78))
  rw [oldBefore100, at100, literal, oldAfter254, gammaAfter254]
  exact numeric
theorem numeric255 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 100 p
  rw [at100] at beforeRange
  have afterRange := bonus_range 122 (HazardPattern.afterPattern 10000 p (.walk 122))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) ∧ bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) ≤ 2 at afterRange
  rw [gammaAfter255] at afterRange
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
theorem local255 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 122 (HazardPattern.afterPattern 10000 p (.walk 122)) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 122) + NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 122))) + bonus 122 (HazardPattern.afterPattern 10000 p (.walk 122)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 122) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) < bonus 100 p at decreasing
  rw [gammaAfter255, at100] at decreasing
  have numeric := numeric255 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122))
  rw [oldBefore100, at100, literal, oldAfter255, gammaAfter255]
  exact numeric
theorem numeric256 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 100 p
  rw [at100] at beforeRange
  have afterRange := bonus_range 122 (HazardPattern.afterPattern 10000 p (.push 122 (.stay 144)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 122 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 122 (.stay 144))) ∧ bonus (HazardPattern.nextHero (.push 122 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 122 (.stay 144))) ≤ 2 at afterRange
  rw [gammaAfter256] at afterRange
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
theorem local256 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 122 (HazardPattern.afterPattern 10000 p (.push 122 (.stay 144))) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 122 (.stay 144)) + NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 122 (.stay 144)))) + bonus 122 (HazardPattern.afterPattern 10000 p (.push 122 (.stay 144))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 122 (.stay 144)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 122 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 122 (.stay 144))) < bonus 100 p at decreasing
  rw [gammaAfter256, at100] at decreasing
  have numeric := numeric256 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 122 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 122 (.stay 144)))
  rw [oldBefore100, at100, literal, oldAfter256, gammaAfter256]
  exact numeric
theorem numeric257 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 100 p
  rw [at100] at beforeRange
  have afterRange := bonus_range 101 (HazardPattern.afterPattern 10000 p (.walk 101))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ∧ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ≤ 2 at afterRange
  rw [gammaAfter257] at afterRange
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
theorem local257 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 101) + NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 101))) + bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 101) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 100 p at decreasing
  rw [gammaAfter257, at100] at decreasing
  have numeric := numeric257 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101))
  rw [oldBefore100, at100, literal, oldAfter257, gammaAfter257]
  exact numeric
theorem numeric258 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 100 p
  rw [at100] at beforeRange
  have afterRange := bonus_range 101 (HazardPattern.afterPattern 10000 p (.push 101 (.stay 102)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 101 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 102))) ∧ bonus (HazardPattern.nextHero (.push 101 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 102))) ≤ 2 at afterRange
  rw [gammaAfter258] at afterRange
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
theorem local258 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 101 (HazardPattern.afterPattern 10000 p (.push 101 (.stay 102))) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 101 (.stay 102)) + NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 101 (.stay 102)))) + bonus 101 (HazardPattern.afterPattern 10000 p (.push 101 (.stay 102))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 101 (.stay 102)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 101 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 102))) < bonus 100 p at decreasing
  rw [gammaAfter258, at100] at decreasing
  have numeric := numeric258 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 101 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 102)))
  rw [oldBefore100, at100, literal, oldAfter258, gammaAfter258]
  exact numeric
theorem numeric259 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 100 p
  rw [at100] at beforeRange
  have afterRange := bonus_range 79 (HazardPattern.afterPattern 10000 p (.walk 79))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) ∧ bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) ≤ 2 at afterRange
  rw [gammaAfter259] at afterRange
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
theorem local259 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 79 (HazardPattern.afterPattern 10000 p (.walk 79)) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 79) + NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 79))) + bonus 79 (HazardPattern.afterPattern 10000 p (.walk 79)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 79) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) < bonus 100 p at decreasing
  rw [gammaAfter259, at100] at decreasing
  have numeric := numeric259 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79))
  rw [oldBefore100, at100, literal, oldAfter259, gammaAfter259]
  exact numeric
theorem numeric260 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 100 p
  rw [at100] at beforeRange
  have afterRange := bonus_range 123 (HazardPattern.afterPattern 10000 p (.walk 123))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ∧ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ≤ 2 at afterRange
  rw [gammaAfter260] at afterRange
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
theorem local260 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 123) + NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) + bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 123) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 100 p at decreasing
  rw [gammaAfter260, at100] at decreasing
  have numeric := numeric260 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123))
  rw [oldBefore100, at100, literal, oldAfter260, gammaAfter260]
  exact numeric
theorem numeric261 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 101 p
  rw [at101] at beforeRange
  have afterRange := bonus_range 79 (HazardPattern.afterPattern 10000 p (.walk 79))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) ∧ bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) ≤ 2 at afterRange
  rw [gammaAfter261] at afterRange
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
theorem local261 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 79 (HazardPattern.afterPattern 10000 p (.walk 79)) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 79) + NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 79))) + bonus 79 (HazardPattern.afterPattern 10000 p (.walk 79)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 79) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) < bonus 101 p at decreasing
  rw [gammaAfter261, at101] at decreasing
  have numeric := numeric261 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79))
  rw [oldBefore101, at101, literal, oldAfter261, gammaAfter261]
  exact numeric
theorem numeric262 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 101 p
  rw [at101] at beforeRange
  have afterRange := bonus_range 123 (HazardPattern.afterPattern 10000 p (.walk 123))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ∧ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ≤ 2 at afterRange
  rw [gammaAfter262] at afterRange
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
theorem local262 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 123) + NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) + bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 123) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 101 p at decreasing
  rw [gammaAfter262, at101] at decreasing
  have numeric := numeric262 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123))
  rw [oldBefore101, at101, literal, oldAfter262, gammaAfter262]
  exact numeric
theorem numeric263 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 101 p
  rw [at101] at beforeRange
  have afterRange := bonus_range 123 (HazardPattern.afterPattern 10000 p (.push 123 (.stay 145)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 123 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 145))) ∧ bonus (HazardPattern.nextHero (.push 123 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 145))) ≤ 2 at afterRange
  rw [gammaAfter263] at afterRange
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
theorem local263 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 123 (HazardPattern.afterPattern 10000 p (.push 123 (.stay 145))) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 123 (.stay 145)) + NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 123 (.stay 145)))) + bonus 123 (HazardPattern.afterPattern 10000 p (.push 123 (.stay 145))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 123 (.stay 145)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 123 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 145))) < bonus 101 p at decreasing
  rw [gammaAfter263, at101] at decreasing
  have numeric := numeric263 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 123 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 145)))
  rw [oldBefore101, at101, literal, oldAfter263, gammaAfter263]
  exact numeric
theorem numeric264 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 101 p
  rw [at101] at beforeRange
  have afterRange := bonus_range 102 (HazardPattern.afterPattern 10000 p (.walk 102))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ∧ bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) ≤ 2 at afterRange
  rw [gammaAfter264] at afterRange
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
theorem local264 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 102) + NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 102))) + bonus 102 (HazardPattern.afterPattern 10000 p (.walk 102)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 102) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) < bonus 101 p at decreasing
  rw [gammaAfter264, at101] at decreasing
  have numeric := numeric264 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102))
  rw [oldBefore101, at101, literal, oldAfter264, gammaAfter264]
  exact numeric
theorem numeric265 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 101 p
  rw [at101] at beforeRange
  have afterRange := bonus_range 102 (HazardPattern.afterPattern 10000 p (.push 102 (.stay 103)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 102 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 103))) ∧ bonus (HazardPattern.nextHero (.push 102 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 103))) ≤ 2 at afterRange
  rw [gammaAfter265] at afterRange
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
theorem local265 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 102 (HazardPattern.afterPattern 10000 p (.push 102 (.stay 103))) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 102 (.stay 103)) + NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 102 (.stay 103)))) + bonus 102 (HazardPattern.afterPattern 10000 p (.push 102 (.stay 103))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 102 (.stay 103)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 102 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 103))) < bonus 101 p at decreasing
  rw [gammaAfter265, at101] at decreasing
  have numeric := numeric265 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 102 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 103)))
  rw [oldBefore101, at101, literal, oldAfter265, gammaAfter265]
  exact numeric
theorem numeric266 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 101 p
  rw [at101] at beforeRange
  have afterRange := bonus_range 100 (HazardPattern.afterPattern 10000 p (.walk 100))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) ∧ bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) ≤ 2 at afterRange
  rw [gammaAfter266] at afterRange
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
theorem local266 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 100 (HazardPattern.afterPattern 10000 p (.walk 100)) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 100) + NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 100))) + bonus 100 (HazardPattern.afterPattern 10000 p (.walk 100)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 100) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) < bonus 101 p at decreasing
  rw [gammaAfter266, at101] at decreasing
  have numeric := numeric266 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100))
  rw [oldBefore101, at101, literal, oldAfter266, gammaAfter266]
  exact numeric
theorem numeric267 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 101 p
  rw [at101] at beforeRange
  have afterRange := bonus_range 80 (HazardPattern.afterPattern 10000 p (.walk 80))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) ∧ bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) ≤ 2 at afterRange
  rw [gammaAfter267] at afterRange
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
theorem local267 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 80 (HazardPattern.afterPattern 10000 p (.walk 80)) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 80) + NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 80))) + bonus 80 (HazardPattern.afterPattern 10000 p (.walk 80)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 80) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) < bonus 101 p at decreasing
  rw [gammaAfter267, at101] at decreasing
  have numeric := numeric267 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80))
  rw [oldBefore101, at101, literal, oldAfter267, gammaAfter267]
  exact numeric
theorem numeric268 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 101 p
  rw [at101] at beforeRange
  have afterRange := bonus_range 78 (HazardPattern.afterPattern 10000 p (.walk 78))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78)) ∧ bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78)) ≤ 2 at afterRange
  rw [gammaAfter268] at afterRange
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
theorem local268 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 78 (HazardPattern.afterPattern 10000 p (.walk 78)) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 78) + NetHack.Sokoban22Refined85.bonus 78 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 78))) + bonus 78 (HazardPattern.afterPattern 10000 p (.walk 78)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 78) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78)) < bonus 101 p at decreasing
  rw [gammaAfter268, at101] at decreasing
  have numeric := numeric268 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78))
  rw [oldBefore101, at101, literal, oldAfter268, gammaAfter268]
  exact numeric
theorem numeric269 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 101 p
  rw [at101] at beforeRange
  have afterRange := bonus_range 124 (HazardPattern.afterPattern 10000 p (.walk 124))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ∧ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ≤ 2 at afterRange
  rw [gammaAfter269] at afterRange
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
theorem local269 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 124) + NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) + bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 124) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 101 p at decreasing
  rw [gammaAfter269, at101] at decreasing
  have numeric := numeric269 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124))
  rw [oldBefore101, at101, literal, oldAfter269, gammaAfter269]
  exact numeric
theorem numeric270 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 101 p
  rw [at101] at beforeRange
  have afterRange := bonus_range 122 (HazardPattern.afterPattern 10000 p (.walk 122))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) ∧ bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) ≤ 2 at afterRange
  rw [gammaAfter270] at afterRange
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
theorem local270 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 122 (HazardPattern.afterPattern 10000 p (.walk 122)) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 122) + NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 122))) + bonus 122 (HazardPattern.afterPattern 10000 p (.walk 122)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 122) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) < bonus 101 p at decreasing
  rw [gammaAfter270, at101] at decreasing
  have numeric := numeric270 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122))
  rw [oldBefore101, at101, literal, oldAfter270, gammaAfter270]
  exact numeric
theorem numeric271 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 102 p
  rw [at102] at beforeRange
  have afterRange := bonus_range 80 (HazardPattern.afterPattern 10000 p (.walk 80))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) ∧ bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) ≤ 2 at afterRange
  rw [gammaAfter271] at afterRange
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
theorem local271 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 80 (HazardPattern.afterPattern 10000 p (.walk 80)) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 80) + NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 80))) + bonus 80 (HazardPattern.afterPattern 10000 p (.walk 80)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 80) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) < bonus 102 p at decreasing
  rw [gammaAfter271, at102] at decreasing
  have numeric := numeric271 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80))
  rw [oldBefore102, at102, literal, oldAfter271, gammaAfter271]
  exact numeric
theorem numeric272 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 102 p
  rw [at102] at beforeRange
  have afterRange := bonus_range 124 (HazardPattern.afterPattern 10000 p (.walk 124))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ∧ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ≤ 2 at afterRange
  rw [gammaAfter272] at afterRange
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
theorem local272 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 124) + NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) + bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 124) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 102 p at decreasing
  rw [gammaAfter272, at102] at decreasing
  have numeric := numeric272 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124))
  rw [oldBefore102, at102, literal, oldAfter272, gammaAfter272]
  exact numeric
theorem numeric273 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 102 p
  rw [at102] at beforeRange
  have afterRange := bonus_range 124 (HazardPattern.afterPattern 10000 p (.push 124 (.stay 146)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 124 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 146))) ∧ bonus (HazardPattern.nextHero (.push 124 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 146))) ≤ 2 at afterRange
  rw [gammaAfter273] at afterRange
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
theorem local273 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 124 (HazardPattern.afterPattern 10000 p (.push 124 (.stay 146))) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 124 (.stay 146)) + NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 124 (.stay 146)))) + bonus 124 (HazardPattern.afterPattern 10000 p (.push 124 (.stay 146))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 124 (.stay 146)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 124 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 146))) < bonus 102 p at decreasing
  rw [gammaAfter273, at102] at decreasing
  have numeric := numeric273 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 124 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 146)))
  rw [oldBefore102, at102, literal, oldAfter273, gammaAfter273]
  exact numeric
theorem numeric274 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 102 p
  rw [at102] at beforeRange
  have afterRange := bonus_range 103 (HazardPattern.afterPattern 10000 p (.walk 103))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ∧ bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) ≤ 2 at afterRange
  rw [gammaAfter274] at afterRange
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
theorem local274 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 103) + NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 103))) + bonus 103 (HazardPattern.afterPattern 10000 p (.walk 103)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 103) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) < bonus 102 p at decreasing
  rw [gammaAfter274, at102] at decreasing
  have numeric := numeric274 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103))
  rw [oldBefore102, at102, literal, oldAfter274, gammaAfter274]
  exact numeric
theorem numeric275 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 102 p
  rw [at102] at beforeRange
  have afterRange := bonus_range 103 (HazardPattern.afterPattern 10000 p (.push 103 (.stay 104)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 103 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 104))) ∧ bonus (HazardPattern.nextHero (.push 103 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 104))) ≤ 2 at afterRange
  rw [gammaAfter275] at afterRange
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
theorem local275 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 103 (HazardPattern.afterPattern 10000 p (.push 103 (.stay 104))) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 103 (.stay 104)) + NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 103 (.stay 104)))) + bonus 103 (HazardPattern.afterPattern 10000 p (.push 103 (.stay 104))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 103 (.stay 104)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 103 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 104))) < bonus 102 p at decreasing
  rw [gammaAfter275, at102] at decreasing
  have numeric := numeric275 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 103 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 104)))
  rw [oldBefore102, at102, literal, oldAfter275, gammaAfter275]
  exact numeric
theorem numeric276 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 102 p
  rw [at102] at beforeRange
  have afterRange := bonus_range 101 (HazardPattern.afterPattern 10000 p (.walk 101))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ∧ bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) ≤ 2 at afterRange
  rw [gammaAfter276] at afterRange
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
theorem local276 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 101) + NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 101))) + bonus 101 (HazardPattern.afterPattern 10000 p (.walk 101)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 101) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) < bonus 102 p at decreasing
  rw [gammaAfter276, at102] at decreasing
  have numeric := numeric276 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101))
  rw [oldBefore102, at102, literal, oldAfter276, gammaAfter276]
  exact numeric
theorem numeric277 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 102 p
  rw [at102] at beforeRange
  have afterRange := bonus_range 101 (HazardPattern.afterPattern 10000 p (.push 101 (.stay 100)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 101 (.stay 100))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 100))) ∧ bonus (HazardPattern.nextHero (.push 101 (.stay 100))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 100))) ≤ 2 at afterRange
  rw [gammaAfter277] at afterRange
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
theorem local277 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 101 (HazardPattern.afterPattern 10000 p (.push 101 (.stay 100))) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 101 (.stay 100)) + NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 101 (.stay 100)))) + bonus 101 (HazardPattern.afterPattern 10000 p (.push 101 (.stay 100))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 101 (.stay 100)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 101 (.stay 100))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 100))) < bonus 102 p at decreasing
  rw [gammaAfter277, at102] at decreasing
  have numeric := numeric277 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 101 (.stay 100))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 100)))
  rw [oldBefore102, at102, literal, oldAfter277, gammaAfter277]
  exact numeric
theorem numeric278 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 102 p
  rw [at102] at beforeRange
  have afterRange := bonus_range 81 (HazardPattern.afterPattern 10000 p (.walk 81))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) ∧ bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) ≤ 2 at afterRange
  rw [gammaAfter278] at afterRange
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
theorem local278 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 81 (HazardPattern.afterPattern 10000 p (.walk 81)) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 81) + NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 81))) + bonus 81 (HazardPattern.afterPattern 10000 p (.walk 81)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 81) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) < bonus 102 p at decreasing
  rw [gammaAfter278, at102] at decreasing
  have numeric := numeric278 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81))
  rw [oldBefore102, at102, literal, oldAfter278, gammaAfter278]
  exact numeric
theorem numeric279 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 102 p
  rw [at102] at beforeRange
  have afterRange := bonus_range 79 (HazardPattern.afterPattern 10000 p (.walk 79))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) ∧ bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) ≤ 2 at afterRange
  rw [gammaAfter279] at afterRange
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
theorem local279 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 79 (HazardPattern.afterPattern 10000 p (.walk 79)) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 79) + NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 79))) + bonus 79 (HazardPattern.afterPattern 10000 p (.walk 79)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 79) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) < bonus 102 p at decreasing
  rw [gammaAfter279, at102] at decreasing
  have numeric := numeric279 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79))
  rw [oldBefore102, at102, literal, oldAfter279, gammaAfter279]
  exact numeric
end NetHack.Soko22Hazard87
