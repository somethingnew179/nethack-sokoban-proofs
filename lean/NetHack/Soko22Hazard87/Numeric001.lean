import NetHack.Soko22Hazard87.Numeric000
import NetHack.Soko22Hazard87.AndIntroBlocks0027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric70 (p : Pattern) (guard : d55757 p = 1) (decreasing : d2671 p < d3015 p) :
    d47911 p + d3015 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 50 p
  rw [at50] at beforeRange
  have afterRange := bonus_range 27 (HazardPattern.afterPattern 10000 p (.walk 27))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27)) ∧ bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27)) ≤ 2 at afterRange
  rw [gammaAfter70] at afterRange
  have possibilities : (d3015 p = 1 ∧ d2671 p = 0) ∨ (d3015 p = 2 ∧ d2671 p = 0) ∨ (d3015 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1406 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro2847 p beforeEq guard
    have complete := andIntro2705 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro2848 p beforeEq guard
    have complete := andIntro2707 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro2848 p beforeEq guard
    have complete := andIntro2708 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local70 (p : Pattern) (guard : d55757 p = 1)
    (decreasing : bonus 27 (HazardPattern.afterPattern 10000 p (.walk 27)) < bonus 50 p) :
    NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 50 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 27) + NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 27))) + bonus 27 (HazardPattern.afterPattern 10000 p (.walk 27)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 27) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27)) < bonus 50 p at decreasing
  rw [gammaAfter70, at50] at decreasing
  have numeric := numeric70 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27))
  rw [oldBefore50, at50, literal, oldAfter70, gammaAfter70]
  exact numeric
theorem numeric71 (p : Pattern) (guard : d64794 p = 1) (decreasing : d3842 p < d3015 p) :
    d47911 p + d3015 p ≤ (0 : Int) + d47911 p + d3842 p := by
  have beforeRange := bonus_range 50 p
  rw [at50] at beforeRange
  have afterRange := bonus_range 73 (HazardPattern.afterPattern 10000 p (.walk 73))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ∧ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ≤ 2 at afterRange
  rw [gammaAfter71] at afterRange
  have possibilities : (d3015 p = 1 ∧ d3842 p = 0) ∨ (d3015 p = 2 ∧ d3842 p = 0) ∨ (d3015 p = 2 ∧ d3842 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1406 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro2876 p beforeEq guard
    have complete := andIntro2877 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro2878 p beforeEq guard
    have complete := andIntro2877 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro2342 p pair.2
    have combined := andIntro2878 p beforeEq guard
    have complete := andIntro2879 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local71 (p : Pattern) (guard : d64794 p = 1)
    (decreasing : bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 50 p) :
    NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 50 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 73) + NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 73))) + bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 73) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 50 p at decreasing
  rw [gammaAfter71, at50] at decreasing
  have numeric := numeric71 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73))
  rw [oldBefore50, at50, literal, oldAfter71, gammaAfter71]
  exact numeric
theorem numeric72 (p : Pattern) (guard : d64965 p = 1) (decreasing : d3673 p < d3015 p) :
    d47911 p + d3015 p ≤ (0 : Int) + d48087 p + d3673 p := by
  have beforeRange := bonus_range 50 p
  rw [at50] at beforeRange
  have afterRange := bonus_range 71 (HazardPattern.afterPattern 10000 p (.walk 71))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) ∧ bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) ≤ 2 at afterRange
  rw [gammaAfter72] at afterRange
  have possibilities : (d3015 p = 1 ∧ d3673 p = 0) ∨ (d3015 p = 2 ∧ d3673 p = 0) ∨ (d3015 p = 2 ∧ d3673 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1406 p pair.1
    have afterEq := eqIntro2078 p pair.2
    have combined := andIntro2900 p beforeEq guard
    have complete := andIntro2921 p afterEq combined
    have bound := compare2476 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro2078 p pair.2
    have combined := andIntro2922 p beforeEq guard
    have complete := andIntro2923 p combined afterEq
    have bound := compare2477 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro2106 p pair.2
    have combined := andIntro2922 p beforeEq guard
    have complete := andIntro2924 p combined afterEq
    have bound := compare2476 p complete
    omega
theorem local72 (p : Pattern) (guard : d64965 p = 1)
    (decreasing : bonus 71 (HazardPattern.afterPattern 10000 p (.walk 71)) < bonus 50 p) :
    NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 50 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 71) + NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 71))) + bonus 71 (HazardPattern.afterPattern 10000 p (.walk 71)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 71) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) < bonus 50 p at decreasing
  rw [gammaAfter72, at50] at decreasing
  have numeric := numeric72 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71))
  rw [oldBefore50, at50, literal, oldAfter72, gammaAfter72]
  exact numeric
theorem numeric73 (p : Pattern) (guard : d56148 p = 1) (decreasing : d2671 p < d3142 p) :
    d47911 p + d3142 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 51 p
  rw [at51] at beforeRange
  have afterRange := bonus_range 29 (HazardPattern.afterPattern 10000 p (.walk 29))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) ∧ bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) ≤ 2 at afterRange
  rw [gammaAfter73] at afterRange
  have possibilities : (d3142 p = 1 ∧ d2671 p = 0) ∨ (d3142 p = 2 ∧ d2671 p = 0) ∨ (d3142 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1448 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro2925 p beforeEq guard
    have complete := andIntro2946 p afterEq combined
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1016 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro1016 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare9 p complete
    omega
theorem local73 (p : Pattern) (guard : d56148 p = 1)
    (decreasing : bonus 29 (HazardPattern.afterPattern 10000 p (.walk 29)) < bonus 51 p) :
    NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 51 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 29) + NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 29))) + bonus 29 (HazardPattern.afterPattern 10000 p (.walk 29)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 29) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) < bonus 51 p at decreasing
  rw [gammaAfter73, at51] at decreasing
  have numeric := numeric73 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29))
  rw [oldBefore51, at51, literal, oldAfter73, gammaAfter73]
  exact numeric
theorem numeric74 (p : Pattern) (guard : d64793 p = 1) (decreasing : d3842 p < d3142 p) :
    d47911 p + d3142 p ≤ (0 : Int) + d47911 p + d3842 p := by
  have beforeRange := bonus_range 51 p
  rw [at51] at beforeRange
  have afterRange := bonus_range 73 (HazardPattern.afterPattern 10000 p (.walk 73))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ∧ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ≤ 2 at afterRange
  rw [gammaAfter74] at afterRange
  have possibilities : (d3142 p = 1 ∧ d3842 p = 0) ∨ (d3142 p = 2 ∧ d3842 p = 0) ∨ (d3142 p = 2 ∧ d3842 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1448 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro2995 p beforeEq guard
    have complete := andIntro3030 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro3051 p beforeEq guard
    have complete := andIntro2877 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro2342 p pair.2
    have combined := andIntro3051 p beforeEq guard
    have complete := andIntro2879 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local74 (p : Pattern) (guard : d64793 p = 1)
    (decreasing : bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 51 p) :
    NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 51 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 73) + NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 73))) + bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 73) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 51 p at decreasing
  rw [gammaAfter74, at51] at decreasing
  have numeric := numeric74 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73))
  rw [oldBefore51, at51, literal, oldAfter74, gammaAfter74]
  exact numeric
theorem numeric75 (p : Pattern) (guard : d65090 p = 1) (decreasing : d65325 p < d3142 p) :
    d47911 p + d3142 p ≤ (1 : Int) + d47911 p + d65325 p := by
  have beforeRange := bonus_range 51 p
  rw [at51] at beforeRange
  have afterRange := bonus_range 73 (HazardPattern.afterPattern 10000 p (.push 73 (.stay 95)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 73 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 73 (.stay 95))) ∧ bonus (HazardPattern.nextHero (.push 73 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 73 (.stay 95))) ≤ 2 at afterRange
  rw [gammaAfter75] at afterRange
  have possibilities : (d3142 p = 1 ∧ d65325 p = 0) ∨ (d3142 p = 2 ∧ d65325 p = 0) ∨ (d3142 p = 2 ∧ d65325 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1448 p pair.1
    have afterEq := eqIntro2422 p pair.2
    have combined := andIntro3086 p beforeEq guard
    have complete := andIntro3087 p afterEq combined
    have bound := compare2478 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro2422 p pair.2
    have combined := andIntro3088 p beforeEq guard
    have complete := andIntro3147 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro2423 p pair.2
    have combined := andIntro3088 p beforeEq guard
    have complete := andIntro3148 p combined afterEq
    have bound := compare2479 p complete
    omega
theorem local75 (p : Pattern) (guard : d65090 p = 1)
    (decreasing : bonus 73 (HazardPattern.afterPattern 10000 p (.push 73 (.stay 95))) < bonus 51 p) :
    NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 51 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 73 (.stay 95)) + NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 73 (.stay 95)))) + bonus 73 (HazardPattern.afterPattern 10000 p (.push 73 (.stay 95))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 73 (.stay 95)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 73 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 73 (.stay 95))) < bonus 51 p at decreasing
  rw [gammaAfter75, at51] at decreasing
  have numeric := numeric75 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 73 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 73 (.stay 95)))
  rw [oldBefore51, at51, literal, oldAfter75, gammaAfter75]
  exact numeric
theorem numeric76 (p : Pattern) (guard : d56762 p = 1) (decreasing : d2671 p < d3142 p) :
    d47911 p + d3142 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 51 p
  rw [at51] at beforeRange
  have afterRange := bonus_range 52 (HazardPattern.afterPattern 10000 p (.walk 52))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) ∧ bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) ≤ 2 at afterRange
  rw [gammaAfter76] at afterRange
  have possibilities : (d3142 p = 1 ∧ d2671 p = 0) ∨ (d3142 p = 2 ∧ d2671 p = 0) ∨ (d3142 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1448 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro3149 p beforeEq guard
    have complete := andIntro2946 p afterEq combined
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro3150 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro3150 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare9 p complete
    omega
theorem local76 (p : Pattern) (guard : d56762 p = 1)
    (decreasing : bonus 52 (HazardPattern.afterPattern 10000 p (.walk 52)) < bonus 51 p) :
    NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 51 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 52) + NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 52))) + bonus 52 (HazardPattern.afterPattern 10000 p (.walk 52)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 52) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) < bonus 51 p at decreasing
  rw [gammaAfter76, at51] at decreasing
  have numeric := numeric76 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52))
  rw [oldBefore51, at51, literal, oldAfter76, gammaAfter76]
  exact numeric
theorem numeric77 (p : Pattern) (guard : d55892 p = 1) (decreasing : d3015 p < d3142 p) :
    d47911 p + d3142 p ≤ (0 : Int) + d47911 p + d3015 p := by
  have beforeRange := bonus_range 51 p
  rw [at51] at beforeRange
  have afterRange := bonus_range 50 (HazardPattern.afterPattern 10000 p (.walk 50))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ∧ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ≤ 2 at afterRange
  rw [gammaAfter77] at afterRange
  have possibilities : (d3142 p = 1 ∧ d3015 p = 0) ∨ (d3142 p = 2 ∧ d3015 p = 0) ∨ (d3142 p = 2 ∧ d3015 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1448 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro3172 p guard beforeEq
    have complete := andIntro3193 p afterEq combined
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro3214 p beforeEq guard
    have complete := andIntro834 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro1406 p pair.2
    have combined := andIntro3214 p beforeEq guard
    have complete := andIntro835 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local77 (p : Pattern) (guard : d55892 p = 1)
    (decreasing : bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 51 p) :
    NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 51 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 50) + NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 50))) + bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 50) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 51 p at decreasing
  rw [gammaAfter77, at51] at decreasing
  have numeric := numeric77 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50))
  rw [oldBefore51, at51, literal, oldAfter77, gammaAfter77]
  exact numeric
theorem numeric78 (p : Pattern) (guard : d64189 p = 1) (decreasing : d65836 p < d3142 p) :
    d47911 p + d3142 p ≤ (1 : Int) + d65730 p + d65836 p := by
  have beforeRange := bonus_range 51 p
  rw [at51] at beforeRange
  have afterRange := bonus_range 50 (HazardPattern.afterPattern 10000 p (.push 50 (.stay 49)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 50 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 50 (.stay 49))) ∧ bonus (HazardPattern.nextHero (.push 50 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 50 (.stay 49))) ≤ 2 at afterRange
  rw [gammaAfter78] at afterRange
  have possibilities : (d3142 p = 1 ∧ d65836 p = 0) ∨ (d3142 p = 2 ∧ d65836 p = 0) ∨ (d3142 p = 2 ∧ d65836 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1448 p pair.1
    have afterEq := eqIntro2444 p pair.2
    have combined := andIntro3235 p beforeEq guard
    have complete := andIntro3236 p combined afterEq
    have bound := compare3390 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro2444 p pair.2
    have combined := andIntro2572 p beforeEq guard
    have complete := andIntro3264 p combined afterEq
    have bound := compare3883 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro2445 p pair.2
    have combined := andIntro2572 p beforeEq guard
    have complete := andIntro3285 p combined afterEq
    have bound := compare4030 p complete
    omega
theorem local78 (p : Pattern) (guard : d64189 p = 1)
    (decreasing : bonus 50 (HazardPattern.afterPattern 10000 p (.push 50 (.stay 49))) < bonus 51 p) :
    NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 51 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 50 (.stay 49)) + NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 50 (.stay 49)))) + bonus 50 (HazardPattern.afterPattern 10000 p (.push 50 (.stay 49))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 50 (.stay 49)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 50 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 50 (.stay 49))) < bonus 51 p at decreasing
  rw [gammaAfter78, at51] at decreasing
  have numeric := numeric78 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 50 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 50 (.stay 49)))
  rw [oldBefore51, at51, literal, oldAfter78, gammaAfter78]
  exact numeric
theorem numeric79 (p : Pattern) (guard : d57566 p = 1) (decreasing : d2671 p < d3142 p) :
    d47911 p + d3142 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 51 p
  rw [at51] at beforeRange
  have afterRange := bonus_range 30 (HazardPattern.afterPattern 10000 p (.walk 30))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 30)) (HazardPattern.afterPattern 10000 p (.walk 30)) ∧ bonus (HazardPattern.nextHero (.walk 30)) (HazardPattern.afterPattern 10000 p (.walk 30)) ≤ 2 at afterRange
  rw [gammaAfter79] at afterRange
  have possibilities : (d3142 p = 1 ∧ d2671 p = 0) ∨ (d3142 p = 2 ∧ d2671 p = 0) ∨ (d3142 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1448 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro3286 p beforeEq guard
    have complete := andIntro2946 p afterEq combined
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1091 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro1091 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare9 p complete
    omega
theorem local79 (p : Pattern) (guard : d57566 p = 1)
    (decreasing : bonus 30 (HazardPattern.afterPattern 10000 p (.walk 30)) < bonus 51 p) :
    NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 51 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 30) + NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 30))) + bonus 30 (HazardPattern.afterPattern 10000 p (.walk 30)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 30) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 30)) (HazardPattern.afterPattern 10000 p (.walk 30)) < bonus 51 p at decreasing
  rw [gammaAfter79, at51] at decreasing
  have numeric := numeric79 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 30)) (HazardPattern.afterPattern 10000 p (.walk 30))
  rw [oldBefore51, at51, literal, oldAfter79, gammaAfter79]
  exact numeric
theorem numeric80 (p : Pattern) (guard : d55894 p = 1) (decreasing : d2671 p < d3142 p) :
    d47911 p + d3142 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 51 p
  rw [at51] at beforeRange
  have afterRange := bonus_range 28 (HazardPattern.afterPattern 10000 p (.walk 28))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) ∧ bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) ≤ 2 at afterRange
  rw [gammaAfter80] at afterRange
  have possibilities : (d3142 p = 1 ∧ d2671 p = 0) ∨ (d3142 p = 2 ∧ d2671 p = 0) ∨ (d3142 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1448 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro3287 p guard beforeEq
    have complete := andIntro2946 p afterEq combined
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro970 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro970 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare9 p complete
    omega
theorem local80 (p : Pattern) (guard : d55894 p = 1)
    (decreasing : bonus 28 (HazardPattern.afterPattern 10000 p (.walk 28)) < bonus 51 p) :
    NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 51 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 28) + NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 28))) + bonus 28 (HazardPattern.afterPattern 10000 p (.walk 28)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 28) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) < bonus 51 p at decreasing
  rw [gammaAfter80, at51] at decreasing
  have numeric := numeric80 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28))
  rw [oldBefore51, at51, literal, oldAfter80, gammaAfter80]
  exact numeric
theorem numeric81 (p : Pattern) (guard : d66091 p = 1) (decreasing : d4025 p < d3142 p) :
    d47911 p + d3142 p ≤ (0 : Int) + d47911 p + d4025 p := by
  have beforeRange := bonus_range 51 p
  rw [at51] at beforeRange
  have afterRange := bonus_range 74 (HazardPattern.afterPattern 10000 p (.walk 74))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) ∧ bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) ≤ 2 at afterRange
  rw [gammaAfter81] at afterRange
  have possibilities : (d3142 p = 1 ∧ d4025 p = 0) ∨ (d3142 p = 2 ∧ d4025 p = 0) ∨ (d3142 p = 2 ∧ d4025 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1448 p pair.1
    have afterEq := eqIntro2480 p pair.2
    have combined := andIntro3351 p beforeEq guard
    have complete := andIntro3386 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro2480 p pair.2
    have combined := andIntro3413 p beforeEq guard
    have complete := andIntro3414 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro2363 p pair.1
    have afterEq := eqIntro2481 p pair.2
    have combined := andIntro3413 p beforeEq guard
    have complete := andIntro3415 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local81 (p : Pattern) (guard : d66091 p = 1)
    (decreasing : bonus 74 (HazardPattern.afterPattern 10000 p (.walk 74)) < bonus 51 p) :
    NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 51 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 74) + NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 74))) + bonus 74 (HazardPattern.afterPattern 10000 p (.walk 74)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 74) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) < bonus 51 p at decreasing
  rw [gammaAfter81, at51] at decreasing
  have numeric := numeric81 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74))
  rw [oldBefore51, at51, literal, oldAfter81, gammaAfter81]
  exact numeric
theorem numeric82 (p : Pattern) (guard : d56771 p = 1) (decreasing : d2671 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 52 p
  rw [at52] at beforeRange
  have afterRange := bonus_range 30 (HazardPattern.afterPattern 10000 p (.walk 30))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 30)) (HazardPattern.afterPattern 10000 p (.walk 30)) ∧ bonus (HazardPattern.nextHero (.walk 30)) (HazardPattern.afterPattern 10000 p (.walk 30)) ≤ 2 at afterRange
  rw [gammaAfter82] at afterRange
  have possibilities : (d2671 p = 1 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1082 p beforeEq guard
    have complete := andIntro722 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1083 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro1083 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare9 p complete
    omega
theorem local82 (p : Pattern) (guard : d56771 p = 1)
    (decreasing : bonus 30 (HazardPattern.afterPattern 10000 p (.walk 30)) < bonus 52 p) :
    NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 52 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 30) + NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 30))) + bonus 30 (HazardPattern.afterPattern 10000 p (.walk 30)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 30) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 30)) (HazardPattern.afterPattern 10000 p (.walk 30)) < bonus 52 p at decreasing
  rw [gammaAfter82, at52] at decreasing
  have numeric := numeric82 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 30)) (HazardPattern.afterPattern 10000 p (.walk 30))
  rw [oldBefore52, at52, literal, oldAfter82, gammaAfter82]
  exact numeric
theorem numeric83 (p : Pattern) (guard : d66275 p = 1) (decreasing : d4025 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d4025 p := by
  have beforeRange := bonus_range 52 p
  rw [at52] at beforeRange
  have afterRange := bonus_range 74 (HazardPattern.afterPattern 10000 p (.walk 74))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) ∧ bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) ≤ 2 at afterRange
  rw [gammaAfter83] at afterRange
  have possibilities : (d2671 p = 1 ∧ d4025 p = 0) ∨ (d2671 p = 2 ∧ d4025 p = 0) ∨ (d2671 p = 2 ∧ d4025 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro2480 p pair.2
    have combined := andIntro3437 p beforeEq guard
    have complete := andIntro3386 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro2480 p pair.2
    have combined := andIntro3458 p beforeEq guard
    have complete := andIntro3414 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro2481 p pair.2
    have combined := andIntro3458 p beforeEq guard
    have complete := andIntro3415 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local83 (p : Pattern) (guard : d66275 p = 1)
    (decreasing : bonus 74 (HazardPattern.afterPattern 10000 p (.walk 74)) < bonus 52 p) :
    NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 52 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 74) + NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 74))) + bonus 74 (HazardPattern.afterPattern 10000 p (.walk 74)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 74) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) < bonus 52 p at decreasing
  rw [gammaAfter83, at52] at decreasing
  have numeric := numeric83 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74))
  rw [oldBefore52, at52, literal, oldAfter83, gammaAfter83]
  exact numeric
theorem numeric84 (p : Pattern) (guard : d66280 p = 1) (decreasing : d66527 p < d2671 p) :
    d47911 p + d2671 p ≤ (1 : Int) + d47911 p + d66527 p := by
  have beforeRange := bonus_range 52 p
  rw [at52] at beforeRange
  have afterRange := bonus_range 74 (HazardPattern.afterPattern 10000 p (.push 74 (.stay 96)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 74 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 74 (.stay 96))) ∧ bonus (HazardPattern.nextHero (.push 74 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 74 (.stay 96))) ≤ 2 at afterRange
  rw [gammaAfter84] at afterRange
  have possibilities : (d2671 p = 1 ∧ d66527 p = 0) ∨ (d2671 p = 2 ∧ d66527 p = 0) ∨ (d2671 p = 2 ∧ d66527 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro2540 p pair.2
    have combined := andIntro3493 p beforeEq guard
    have complete := andIntro3494 p afterEq combined
    have bound := compare4031 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro2540 p pair.2
    have combined := andIntro3495 p beforeEq guard
    have complete := andIntro3554 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro2541 p pair.2
    have combined := andIntro3495 p beforeEq guard
    have complete := andIntro3555 p combined afterEq
    have bound := compare2479 p complete
    omega
theorem local84 (p : Pattern) (guard : d66280 p = 1)
    (decreasing : bonus 74 (HazardPattern.afterPattern 10000 p (.push 74 (.stay 96))) < bonus 52 p) :
    NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 52 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 74 (.stay 96)) + NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 74 (.stay 96)))) + bonus 74 (HazardPattern.afterPattern 10000 p (.push 74 (.stay 96))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 74 (.stay 96)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 74 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 74 (.stay 96))) < bonus 52 p at decreasing
  rw [gammaAfter84, at52] at decreasing
  have numeric := numeric84 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 74 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 74 (.stay 96)))
  rw [oldBefore52, at52, literal, oldAfter84, gammaAfter84]
  exact numeric
theorem numeric85 (p : Pattern) (guard : d56762 p = 1) (decreasing : d3142 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d3142 p := by
  have beforeRange := bonus_range 52 p
  rw [at52] at beforeRange
  have afterRange := bonus_range 51 (HazardPattern.afterPattern 10000 p (.walk 51))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ∧ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ≤ 2 at afterRange
  rw [gammaAfter85] at afterRange
  have possibilities : (d2671 p = 1 ∧ d3142 p = 0) ∨ (d2671 p = 2 ∧ d3142 p = 0) ∨ (d2671 p = 2 ∧ d3142 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro3557 p beforeEq guard
    have complete := andIntro969 p afterEq combined
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro3150 p beforeEq guard
    have complete := andIntro991 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1448 p pair.2
    have combined := andIntro3150 p beforeEq guard
    have complete := andIntro1012 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local85 (p : Pattern) (guard : d56762 p = 1)
    (decreasing : bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 52 p) :
    NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 52 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 51) + NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 51))) + bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 51) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 52 p at decreasing
  rw [gammaAfter85, at52] at decreasing
  have numeric := numeric85 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51))
  rw [oldBefore52, at52, literal, oldAfter85, gammaAfter85]
  exact numeric
theorem numeric86 (p : Pattern) (guard : d64664 p = 1) (decreasing : d67063 p < d2671 p) :
    d47911 p + d2671 p ≤ (1 : Int) + d47911 p + d67063 p := by
  have beforeRange := bonus_range 52 p
  rw [at52] at beforeRange
  have afterRange := bonus_range 51 (HazardPattern.afterPattern 10000 p (.push 51 (.stay 50)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 51 (.stay 50))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 50))) ∧ bonus (HazardPattern.nextHero (.push 51 (.stay 50))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 50))) ≤ 2 at afterRange
  rw [gammaAfter86] at afterRange
  have possibilities : (d2671 p = 1 ∧ d67063 p = 0) ∨ (d2671 p = 2 ∧ d67063 p = 0) ∨ (d2671 p = 2 ∧ d67063 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro2563 p pair.2
    have combined := andIntro3579 p beforeEq guard
    have complete := andIntro3600 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro2563 p pair.2
    have combined := andIntro3621 p beforeEq guard
    have complete := andIntro3622 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro2584 p pair.2
    have combined := andIntro3621 p beforeEq guard
    have complete := andIntro3623 p combined afterEq
    have bound := compare11 p complete
    omega
theorem local86 (p : Pattern) (guard : d64664 p = 1)
    (decreasing : bonus 51 (HazardPattern.afterPattern 10000 p (.push 51 (.stay 50))) < bonus 52 p) :
    NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 52 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 51 (.stay 50)) + NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 51 (.stay 50)))) + bonus 51 (HazardPattern.afterPattern 10000 p (.push 51 (.stay 50))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 51 (.stay 50)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 51 (.stay 50))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 50))) < bonus 52 p at decreasing
  rw [gammaAfter86, at52] at decreasing
  have numeric := numeric86 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 51 (.stay 50))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 50)))
  rw [oldBefore52, at52, literal, oldAfter86, gammaAfter86]
  exact numeric
theorem numeric87 (p : Pattern) (guard : d56764 p = 1) (decreasing : d2671 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 52 p
  rw [at52] at beforeRange
  have afterRange := bonus_range 29 (HazardPattern.afterPattern 10000 p (.walk 29))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) ∧ bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) ≤ 2 at afterRange
  rw [gammaAfter87] at afterRange
  have possibilities : (d2671 p = 1 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1078 p beforeEq guard
    have complete := andIntro722 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1079 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro1079 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare9 p complete
    omega
theorem local87 (p : Pattern) (guard : d56764 p = 1)
    (decreasing : bonus 29 (HazardPattern.afterPattern 10000 p (.walk 29)) < bonus 52 p) :
    NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 52 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 29) + NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 29))) + bonus 29 (HazardPattern.afterPattern 10000 p (.walk 29)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 29) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) < bonus 52 p at decreasing
  rw [gammaAfter87, at52] at decreasing
  have numeric := numeric87 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29))
  rw [oldBefore52, at52, literal, oldAfter87, gammaAfter87]
  exact numeric
theorem numeric88 (p : Pattern) (guard : d67300 p = 1) (decreasing : d3842 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d3842 p := by
  have beforeRange := bonus_range 52 p
  rw [at52] at beforeRange
  have afterRange := bonus_range 73 (HazardPattern.afterPattern 10000 p (.walk 73))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ∧ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ≤ 2 at afterRange
  rw [gammaAfter88] at afterRange
  have possibilities : (d2671 p = 1 ∧ d3842 p = 0) ∨ (d2671 p = 2 ∧ d3842 p = 0) ∨ (d2671 p = 2 ∧ d3842 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro3659 p beforeEq guard
    have complete := andIntro3030 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro3680 p beforeEq guard
    have complete := andIntro2877 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro2342 p pair.2
    have combined := andIntro3680 p beforeEq guard
    have complete := andIntro2879 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local88 (p : Pattern) (guard : d67300 p = 1)
    (decreasing : bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 52 p) :
    NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 52 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 73) + NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 73))) + bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 73) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 52 p at decreasing
  rw [gammaAfter88, at52] at decreasing
  have numeric := numeric88 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73))
  rw [oldBefore52, at52, literal, oldAfter88, gammaAfter88]
  exact numeric
theorem numeric89 (p : Pattern) (guard : d57571 p = 1) (decreasing : d2518 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 67 p
  rw [at67] at beforeRange
  have afterRange := bonus_range 45 (HazardPattern.afterPattern 10000 p (.walk 45))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 45)) (HazardPattern.afterPattern 10000 p (.walk 45)) ∧ bonus (HazardPattern.nextHero (.walk 45)) (HazardPattern.afterPattern 10000 p (.walk 45)) ≤ 2 at afterRange
  rw [gammaAfter89] at afterRange
  have possibilities : (d2518 p = 1 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1092 p beforeEq guard
    have complete := andIntro321 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1093 p beforeEq guard
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro1093 p beforeEq guard
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local89 (p : Pattern) (guard : d57571 p = 1)
    (decreasing : bonus 45 (HazardPattern.afterPattern 10000 p (.walk 45)) < bonus 67 p) :
    NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 67 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 45) + NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 45))) + bonus 45 (HazardPattern.afterPattern 10000 p (.walk 45)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 45) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 45)) (HazardPattern.afterPattern 10000 p (.walk 45)) < bonus 67 p at decreasing
  rw [gammaAfter89, at67] at decreasing
  have numeric := numeric89 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 45)) (HazardPattern.afterPattern 10000 p (.walk 45))
  rw [oldBefore67, at67, literal, oldAfter89, gammaAfter89]
  exact numeric
theorem numeric90 (p : Pattern) (guard : d67301 p = 1) (decreasing : d4334 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d4334 p := by
  have beforeRange := bonus_range 67 p
  rw [at67] at beforeRange
  have afterRange := bonus_range 89 (HazardPattern.afterPattern 10000 p (.walk 89))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89)) ∧ bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89)) ≤ 2 at afterRange
  rw [gammaAfter90] at afterRange
  have possibilities : (d2518 p = 1 ∧ d4334 p = 0) ∨ (d2518 p = 2 ∧ d4334 p = 0) ∨ (d2518 p = 2 ∧ d4334 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro2633 p pair.2
    have combined := andIntro3729 p beforeEq guard
    have complete := andIntro3778 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro2633 p pair.2
    have combined := andIntro3779 p beforeEq guard
    have complete := andIntro3828 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro2682 p pair.2
    have combined := andIntro3779 p beforeEq guard
    have complete := andIntro3877 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local90 (p : Pattern) (guard : d67301 p = 1)
    (decreasing : bonus 89 (HazardPattern.afterPattern 10000 p (.walk 89)) < bonus 67 p) :
    NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 67 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 89) + NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 89))) + bonus 89 (HazardPattern.afterPattern 10000 p (.walk 89)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 89) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89)) < bonus 67 p at decreasing
  rw [gammaAfter90, at67] at decreasing
  have numeric := numeric90 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89))
  rw [oldBefore67, at67, literal, oldAfter90, gammaAfter90]
  exact numeric
theorem numeric91 (p : Pattern) (guard : d67924 p = 1) (decreasing : d0 p < d2518 p) :
    d47866 p + d2518 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 67 p
  rw [at67] at beforeRange
  have afterRange := bonus_range 89 (HazardPattern.afterPattern 10000 p (.push 89 (.stay 111)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 89 (.stay 111))) (HazardPattern.afterPattern 10000 p (.push 89 (.stay 111))) ∧ bonus (HazardPattern.nextHero (.push 89 (.stay 111))) (HazardPattern.afterPattern 10000 p (.push 89 (.stay 111))) ≤ 2 at afterRange
  rw [gammaAfter91] at afterRange
  have possibilities : (d2518 p = 1 ∧ d0 p = 0) ∨ (d2518 p = 2 ∧ d0 p = 0) ∨ (d2518 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro3969 p beforeEq guard
    have complete := andIntro3970 p afterEq combined
    have bound := compare4032 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro4003 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro4003 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2 p complete
    omega
theorem local91 (p : Pattern) (guard : d67924 p = 1)
    (decreasing : bonus 89 (HazardPattern.afterPattern 10000 p (.push 89 (.stay 111))) < bonus 67 p) :
    NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 67 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 89 (.stay 111)) + NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 89 (.stay 111)))) + bonus 89 (HazardPattern.afterPattern 10000 p (.push 89 (.stay 111))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 89 (.stay 111)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 89 (.stay 111))) (HazardPattern.afterPattern 10000 p (.push 89 (.stay 111))) < bonus 67 p at decreasing
  rw [gammaAfter91, at67] at decreasing
  have numeric := numeric91 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 89 (.stay 111))) (HazardPattern.afterPattern 10000 p (.push 89 (.stay 111)))
  rw [oldBefore67, at67, literal, oldAfter91, gammaAfter91]
  exact numeric
theorem numeric92 (p : Pattern) (guard : d58745 p = 1) (decreasing : d2518 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 67 p
  rw [at67] at beforeRange
  have afterRange := bonus_range 46 (HazardPattern.afterPattern 10000 p (.walk 46))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) ∧ bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) ≤ 2 at afterRange
  rw [gammaAfter92] at afterRange
  have possibilities : (d2518 p = 1 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1199 p beforeEq guard
    have complete := andIntro321 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1200 p beforeEq guard
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro1200 p beforeEq guard
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local92 (p : Pattern) (guard : d58745 p = 1)
    (decreasing : bonus 46 (HazardPattern.afterPattern 10000 p (.walk 46)) < bonus 67 p) :
    NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 67 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 46) + NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 46))) + bonus 46 (HazardPattern.afterPattern 10000 p (.walk 46)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 46) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) < bonus 67 p at decreasing
  rw [gammaAfter92, at67] at decreasing
  have numeric := numeric92 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46))
  rw [oldBefore67, at67, literal, oldAfter92, gammaAfter92]
  exact numeric
theorem numeric93 (p : Pattern) (guard : d68223 p = 1) (decreasing : d4650 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d4650 p := by
  have beforeRange := bonus_range 67 p
  rw [at67] at beforeRange
  have afterRange := bonus_range 90 (HazardPattern.afterPattern 10000 p (.walk 90))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) ∧ bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) ≤ 2 at afterRange
  rw [gammaAfter93] at afterRange
  have possibilities : (d2518 p = 1 ∧ d4650 p = 0) ∨ (d2518 p = 2 ∧ d4650 p = 0) ∨ (d2518 p = 2 ∧ d4650 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro2731 p pair.2
    have combined := andIntro4090 p beforeEq guard
    have complete := andIntro4139 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro2731 p pair.2
    have combined := andIntro4172 p beforeEq guard
    have complete := andIntro4173 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro2732 p pair.2
    have combined := andIntro4172 p beforeEq guard
    have complete := andIntro4174 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local93 (p : Pattern) (guard : d68223 p = 1)
    (decreasing : bonus 90 (HazardPattern.afterPattern 10000 p (.walk 90)) < bonus 67 p) :
    NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 67 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 90) + NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 90))) + bonus 90 (HazardPattern.afterPattern 10000 p (.walk 90)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 90) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) < bonus 67 p at decreasing
  rw [gammaAfter93, at67] at decreasing
  have numeric := numeric93 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90))
  rw [oldBefore67, at67, literal, oldAfter93, gammaAfter93]
  exact numeric
theorem numeric94 (p : Pattern) (guard : d58432 p = 1) (decreasing : d2518 p < d3318 p) :
    d47866 p + d3318 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 69 p
  rw [at69] at beforeRange
  have afterRange := bonus_range 47 (HazardPattern.afterPattern 10000 p (.walk 47))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) ∧ bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) ≤ 2 at afterRange
  rw [gammaAfter94] at afterRange
  have possibilities : (d3318 p = 1 ∧ d2518 p = 0) ∨ (d3318 p = 2 ∧ d2518 p = 0) ∨ (d3318 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1787 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro4175 p guard beforeEq
    have complete := andIntro4196 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1203 p beforeEq guard
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro1203 p beforeEq guard
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local94 (p : Pattern) (guard : d58432 p = 1)
    (decreasing : bonus 47 (HazardPattern.afterPattern 10000 p (.walk 47)) < bonus 69 p) :
    NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 69 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 47) + NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 47))) + bonus 47 (HazardPattern.afterPattern 10000 p (.walk 47)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 47) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) < bonus 69 p at decreasing
  rw [gammaAfter94, at69] at decreasing
  have numeric := numeric94 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47))
  rw [oldBefore69, at69, literal, oldAfter94, gammaAfter94]
  exact numeric
theorem numeric95 (p : Pattern) (guard : d53870 p = 1) (decreasing : d0 p < d3318 p) :
    d47866 p + d3318 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 69 p
  rw [at69] at beforeRange
  have afterRange := bonus_range 47 (HazardPattern.afterPattern 10000 p (.push 47 (.stay 25)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 47 (.stay 25))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 25))) ∧ bonus (HazardPattern.nextHero (.push 47 (.stay 25))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 25))) ≤ 2 at afterRange
  rw [gammaAfter95] at afterRange
  have possibilities : (d3318 p = 1 ∧ d0 p = 0) ∨ (d3318 p = 2 ∧ d0 p = 0) ∨ (d3318 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1787 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro4198 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro425 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro425 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2 p complete
    omega
theorem local95 (p : Pattern) (guard : d53870 p = 1)
    (decreasing : bonus 47 (HazardPattern.afterPattern 10000 p (.push 47 (.stay 25))) < bonus 69 p) :
    NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 69 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 47 (.stay 25)) + NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 47 (.stay 25)))) + bonus 47 (HazardPattern.afterPattern 10000 p (.push 47 (.stay 25))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 47 (.stay 25)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 47 (.stay 25))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 25))) < bonus 69 p at decreasing
  rw [gammaAfter95, at69] at decreasing
  have numeric := numeric95 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 47 (.stay 25))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 25)))
  rw [oldBefore69, at69, literal, oldAfter95, gammaAfter95]
  exact numeric
theorem numeric96 (p : Pattern) (guard : d68751 p = 1) (decreasing : d5349 p < d3318 p) :
    d47866 p + d3318 p ≤ (0 : Int) + d47866 p + d5349 p := by
  have beforeRange := bonus_range 69 p
  rw [at69] at beforeRange
  have afterRange := bonus_range 91 (HazardPattern.afterPattern 10000 p (.walk 91))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) ∧ bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) ≤ 2 at afterRange
  rw [gammaAfter96] at afterRange
  have possibilities : (d3318 p = 1 ∧ d5349 p = 0) ∨ (d3318 p = 2 ∧ d5349 p = 0) ∨ (d3318 p = 2 ∧ d5349 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1787 p pair.1
    have afterEq := eqIntro2844 p pair.2
    have combined := andIntro4259 p beforeEq guard
    have complete := andIntro4320 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro2844 p pair.2
    have combined := andIntro4352 p beforeEq guard
    have complete := andIntro4401 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro2893 p pair.2
    have combined := andIntro4352 p beforeEq guard
    have complete := andIntro4450 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local96 (p : Pattern) (guard : d68751 p = 1)
    (decreasing : bonus 91 (HazardPattern.afterPattern 10000 p (.walk 91)) < bonus 69 p) :
    NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 69 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 91) + NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 91))) + bonus 91 (HazardPattern.afterPattern 10000 p (.walk 91)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 91) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) < bonus 69 p at decreasing
  rw [gammaAfter96, at69] at decreasing
  have numeric := numeric96 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91))
  rw [oldBefore69, at69, literal, oldAfter96, gammaAfter96]
  exact numeric
theorem numeric97 (p : Pattern) (guard : d70148 p = 1) (decreasing : d70809 p < d3318 p) :
    d47866 p + d3318 p ≤ (0 : Int) + d47866 p + d70809 p := by
  have beforeRange := bonus_range 69 p
  rw [at69] at beforeRange
  have afterRange := bonus_range 91 (HazardPattern.afterPattern 10000 p (.push 91 (.stay 113)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 91 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 91 (.stay 113))) ∧ bonus (HazardPattern.nextHero (.push 91 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 91 (.stay 113))) ≤ 2 at afterRange
  rw [gammaAfter97] at afterRange
  have possibilities : (d3318 p = 1 ∧ d70809 p = 0) ∨ (d3318 p = 2 ∧ d70809 p = 0) ∨ (d3318 p = 2 ∧ d70809 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1787 p pair.1
    have afterEq := eqIntro3032 p pair.2
    have combined := andIntro4536 p beforeEq guard
    have complete := andIntro4652 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro3032 p pair.2
    have combined := andIntro4687 p beforeEq guard
    have complete := andIntro4736 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro3094 p pair.2
    have combined := andIntro4687 p beforeEq guard
    have complete := andIntro4780 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local97 (p : Pattern) (guard : d70148 p = 1)
    (decreasing : bonus 91 (HazardPattern.afterPattern 10000 p (.push 91 (.stay 113))) < bonus 69 p) :
    NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 69 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 91 (.stay 113)) + NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 91 (.stay 113)))) + bonus 91 (HazardPattern.afterPattern 10000 p (.push 91 (.stay 113))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 91 (.stay 113)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 91 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 91 (.stay 113))) < bonus 69 p at decreasing
  rw [gammaAfter97, at69] at decreasing
  have numeric := numeric97 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 91 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 91 (.stay 113)))
  rw [oldBefore69, at69, literal, oldAfter97, gammaAfter97]
  exact numeric
theorem numeric98 (p : Pattern) (guard : d61358 p = 1) (decreasing : d3496 p < d3318 p) :
    d47866 p + d3318 p ≤ (0 : Int) + d47866 p + d3496 p := by
  have beforeRange := bonus_range 69 p
  rw [at69] at beforeRange
  have afterRange := bonus_range 70 (HazardPattern.afterPattern 10000 p (.walk 70))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ∧ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ≤ 2 at afterRange
  rw [gammaAfter98] at afterRange
  have possibilities : (d3318 p = 1 ∧ d3496 p = 0) ∨ (d3318 p = 2 ∧ d3496 p = 0) ∨ (d3318 p = 2 ∧ d3496 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1787 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro4802 p beforeEq guard
    have complete := andIntro4823 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro4844 p beforeEq guard
    have complete := andIntro1577 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro1978 p pair.2
    have combined := andIntro4844 p beforeEq guard
    have complete := andIntro1598 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local98 (p : Pattern) (guard : d61358 p = 1)
    (decreasing : bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 69 p) :
    NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 69 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 70) + NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 70))) + bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 70) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 69 p at decreasing
  rw [gammaAfter98, at69] at decreasing
  have numeric := numeric98 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70))
  rw [oldBefore69, at69, literal, oldAfter98, gammaAfter98]
  exact numeric
theorem numeric99 (p : Pattern) (guard : d72603 p = 1) (decreasing : d72763 p < d3318 p) :
    d47866 p + d3318 p ≤ (0 : Int) + d72606 p + d72763 p := by
  have beforeRange := bonus_range 69 p
  rw [at69] at beforeRange
  have afterRange := bonus_range 70 (HazardPattern.afterPattern 10000 p (.push 70 (.stay 71)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 70 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 70 (.stay 71))) ∧ bonus (HazardPattern.nextHero (.push 70 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 70 (.stay 71))) ≤ 2 at afterRange
  rw [gammaAfter99] at afterRange
  have possibilities : (d3318 p = 1 ∧ d72763 p = 0) ∨ (d3318 p = 2 ∧ d72763 p = 0) ∨ (d3318 p = 2 ∧ d72763 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1787 p pair.1
    have afterEq := eqIntro3116 p pair.2
    have combined := andIntro4882 p beforeEq guard
    have complete := andIntro4912 p afterEq combined
    have bound := compare4033 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro3116 p pair.2
    have combined := andIntro4947 p beforeEq guard
    have complete := andIntro4975 p combined afterEq
    have bound := compare4034 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro3137 p pair.2
    have combined := andIntro4947 p beforeEq guard
    have complete := andIntro5003 p combined afterEq
    have bound := compare4033 p complete
    omega
theorem local99 (p : Pattern) (guard : d72603 p = 1)
    (decreasing : bonus 70 (HazardPattern.afterPattern 10000 p (.push 70 (.stay 71))) < bonus 69 p) :
    NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 69 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 70 (.stay 71)) + NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 70 (.stay 71)))) + bonus 70 (HazardPattern.afterPattern 10000 p (.push 70 (.stay 71))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 70 (.stay 71)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 70 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 70 (.stay 71))) < bonus 69 p at decreasing
  rw [gammaAfter99, at69] at decreasing
  have numeric := numeric99 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 70 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 70 (.stay 71)))
  rw [oldBefore69, at69, literal, oldAfter99, gammaAfter99]
  exact numeric
theorem numeric100 (p : Pattern) (guard : d62827 p = 1) (decreasing : d2782 p < d3318 p) :
    d47866 p + d3318 p ≤ (0 : Int) + d48080 p + d2782 p := by
  have beforeRange := bonus_range 69 p
  rw [at69] at beforeRange
  have afterRange := bonus_range 48 (HazardPattern.afterPattern 10000 p (.walk 48))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ∧ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ≤ 2 at afterRange
  rw [gammaAfter100] at afterRange
  have possibilities : (d3318 p = 1 ∧ d2782 p = 0) ∨ (d3318 p = 2 ∧ d2782 p = 0) ∨ (d3318 p = 2 ∧ d2782 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1787 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro5025 p beforeEq guard
    have complete := andIntro5046 p afterEq combined
    have bound := compare3 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro5067 p beforeEq guard
    have complete := andIntro512 p afterEq combined
    have bound := compare4 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro1166 p pair.2
    have combined := andIntro5067 p beforeEq guard
    have complete := andIntro533 p afterEq combined
    have bound := compare3 p complete
    omega
theorem local100 (p : Pattern) (guard : d62827 p = 1)
    (decreasing : bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 69 p) :
    NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 69 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 48) + NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 48))) + bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 48) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 69 p at decreasing
  rw [gammaAfter100, at69] at decreasing
  have numeric := numeric100 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48))
  rw [oldBefore69, at69, literal, oldAfter100, gammaAfter100]
  exact numeric
theorem numeric101 (p : Pattern) (guard : d58433 p = 1) (decreasing : d2518 p < d3318 p) :
    d47866 p + d3318 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 69 p
  rw [at69] at beforeRange
  have afterRange := bonus_range 46 (HazardPattern.afterPattern 10000 p (.walk 46))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) ∧ bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) ≤ 2 at afterRange
  rw [gammaAfter101] at afterRange
  have possibilities : (d3318 p = 1 ∧ d2518 p = 0) ∨ (d3318 p = 2 ∧ d2518 p = 0) ∨ (d3318 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1787 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro5068 p guard beforeEq
    have complete := andIntro4196 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1156 p beforeEq guard
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro1156 p beforeEq guard
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local101 (p : Pattern) (guard : d58433 p = 1)
    (decreasing : bonus 46 (HazardPattern.afterPattern 10000 p (.walk 46)) < bonus 69 p) :
    NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 69 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 46) + NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 46))) + bonus 46 (HazardPattern.afterPattern 10000 p (.walk 46)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 46) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) < bonus 69 p at decreasing
  rw [gammaAfter101, at69] at decreasing
  have numeric := numeric101 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46))
  rw [oldBefore69, at69, literal, oldAfter101, gammaAfter101]
  exact numeric
theorem numeric102 (p : Pattern) (guard : d73191 p = 1) (decreasing : d4650 p < d3318 p) :
    d47866 p + d3318 p ≤ (0 : Int) + d47866 p + d4650 p := by
  have beforeRange := bonus_range 69 p
  rw [at69] at beforeRange
  have afterRange := bonus_range 90 (HazardPattern.afterPattern 10000 p (.walk 90))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) ∧ bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) ≤ 2 at afterRange
  rw [gammaAfter102] at afterRange
  have possibilities : (d3318 p = 1 ∧ d4650 p = 0) ∨ (d3318 p = 2 ∧ d4650 p = 0) ∨ (d3318 p = 2 ∧ d4650 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1787 p pair.1
    have afterEq := eqIntro2731 p pair.2
    have combined := andIntro5131 p beforeEq guard
    have complete := andIntro5180 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro2731 p pair.2
    have combined := andIntro5215 p beforeEq guard
    have complete := andIntro4173 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro2753 p pair.1
    have afterEq := eqIntro2732 p pair.2
    have combined := andIntro5215 p beforeEq guard
    have complete := andIntro4174 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local102 (p : Pattern) (guard : d73191 p = 1)
    (decreasing : bonus 90 (HazardPattern.afterPattern 10000 p (.walk 90)) < bonus 69 p) :
    NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 69 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 90) + NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 90))) + bonus 90 (HazardPattern.afterPattern 10000 p (.walk 90)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 90) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) < bonus 69 p at decreasing
  rw [gammaAfter102, at69] at decreasing
  have numeric := numeric102 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90))
  rw [oldBefore69, at69, literal, oldAfter102, gammaAfter102]
  exact numeric
theorem numeric103 (p : Pattern) (guard : d61807 p = 1) (decreasing : d2782 p < d3496 p) :
    d47866 p + d3496 p ≤ (0 : Int) + d48080 p + d2782 p := by
  have beforeRange := bonus_range 70 p
  rw [at70] at beforeRange
  have afterRange := bonus_range 48 (HazardPattern.afterPattern 10000 p (.walk 48))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ∧ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ≤ 2 at afterRange
  rw [gammaAfter103] at afterRange
  have possibilities : (d3496 p = 1 ∧ d2782 p = 0) ∨ (d3496 p = 2 ∧ d2782 p = 0) ∨ (d3496 p = 2 ∧ d2782 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1978 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro5216 p beforeEq guard
    have complete := andIntro5238 p afterEq combined
    have bound := compare3 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro5239 p beforeEq guard
    have complete := andIntro5260 p afterEq combined
    have bound := compare4 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro1166 p pair.2
    have combined := andIntro5239 p beforeEq guard
    have complete := andIntro5281 p afterEq combined
    have bound := compare3 p complete
    omega
theorem local103 (p : Pattern) (guard : d61807 p = 1)
    (decreasing : bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 70 p) :
    NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 70 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 48) + NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 48))) + bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 48) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 70 p at decreasing
  rw [gammaAfter103, at70] at decreasing
  have numeric := numeric103 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48))
  rw [oldBefore70, at70, literal, oldAfter103, gammaAfter103]
  exact numeric
theorem numeric104 (p : Pattern) (guard : d62374 p = 1) (decreasing : d3673 p < d3496 p) :
    d47866 p + d3496 p ≤ (0 : Int) + d48087 p + d3673 p := by
  have beforeRange := bonus_range 70 p
  rw [at70] at beforeRange
  have afterRange := bonus_range 71 (HazardPattern.afterPattern 10000 p (.walk 71))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) ∧ bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) ≤ 2 at afterRange
  rw [gammaAfter104] at afterRange
  have possibilities : (d3496 p = 1 ∧ d3673 p = 0) ∨ (d3496 p = 2 ∧ d3673 p = 0) ∨ (d3496 p = 2 ∧ d3673 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1978 p pair.1
    have afterEq := eqIntro2078 p pair.2
    have combined := andIntro5303 p beforeEq guard
    have complete := andIntro5324 p afterEq combined
    have bound := compare4035 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro2078 p pair.2
    have combined := andIntro5345 p beforeEq guard
    have complete := andIntro2923 p combined afterEq
    have bound := compare4036 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro2106 p pair.2
    have combined := andIntro5345 p beforeEq guard
    have complete := andIntro2924 p combined afterEq
    have bound := compare4035 p complete
    omega
theorem local104 (p : Pattern) (guard : d62374 p = 1)
    (decreasing : bonus 71 (HazardPattern.afterPattern 10000 p (.walk 71)) < bonus 70 p) :
    NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 70 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 71) + NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 71))) + bonus 71 (HazardPattern.afterPattern 10000 p (.walk 71)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 71) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) < bonus 70 p at decreasing
  rw [gammaAfter104, at70] at decreasing
  have numeric := numeric104 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71))
  rw [oldBefore70, at70, literal, oldAfter104, gammaAfter104]
  exact numeric
theorem numeric105 (p : Pattern) (guard : d61358 p = 1) (decreasing : d3318 p < d3496 p) :
    d47866 p + d3496 p ≤ (0 : Int) + d47866 p + d3318 p := by
  have beforeRange := bonus_range 70 p
  rw [at70] at beforeRange
  have afterRange := bonus_range 69 (HazardPattern.afterPattern 10000 p (.walk 69))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) ∧ bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) ≤ 2 at afterRange
  rw [gammaAfter105] at afterRange
  have possibilities : (d3496 p = 1 ∧ d3318 p = 0) ∨ (d3496 p = 2 ∧ d3318 p = 0) ∨ (d3496 p = 2 ∧ d3318 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1978 p pair.1
    have afterEq := eqIntro1766 p pair.2
    have combined := andIntro5366 p guard beforeEq
    have complete := andIntro5388 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro1766 p pair.2
    have combined := andIntro5389 p guard beforeEq
    have complete := andIntro5410 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro1787 p pair.2
    have combined := andIntro5389 p guard beforeEq
    have complete := andIntro5431 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local105 (p : Pattern) (guard : d61358 p = 1)
    (decreasing : bonus 69 (HazardPattern.afterPattern 10000 p (.walk 69)) < bonus 70 p) :
    NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 70 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 69) + NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 69))) + bonus 69 (HazardPattern.afterPattern 10000 p (.walk 69)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 69) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) < bonus 70 p at decreasing
  rw [gammaAfter105, at70] at decreasing
  have numeric := numeric105 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69))
  rw [oldBefore70, at70, literal, oldAfter105, gammaAfter105]
  exact numeric
theorem numeric106 (p : Pattern) (guard : d64542 p = 1) (decreasing : d2895 p < d3496 p) :
    d47866 p + d3496 p ≤ (0 : Int) + d48083 p + d2895 p := by
  have beforeRange := bonus_range 70 p
  rw [at70] at beforeRange
  have afterRange := bonus_range 49 (HazardPattern.afterPattern 10000 p (.walk 49))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) ∧ bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) ≤ 2 at afterRange
  rw [gammaAfter106] at afterRange
  have possibilities : (d3496 p = 1 ∧ d2895 p = 0) ∨ (d3496 p = 2 ∧ d2895 p = 0) ∨ (d3496 p = 2 ∧ d2895 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1978 p pair.1
    have afterEq := eqIntro1209 p pair.2
    have combined := andIntro5432 p beforeEq guard
    have complete := andIntro5454 p afterEq combined
    have bound := compare4037 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro1209 p pair.2
    have combined := andIntro5455 p beforeEq guard
    have complete := andIntro5476 p afterEq combined
    have bound := compare4038 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro1258 p pair.2
    have combined := andIntro5455 p beforeEq guard
    have complete := andIntro5497 p afterEq combined
    have bound := compare4037 p complete
    omega
theorem local106 (p : Pattern) (guard : d64542 p = 1)
    (decreasing : bonus 49 (HazardPattern.afterPattern 10000 p (.walk 49)) < bonus 70 p) :
    NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 70 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 49) + NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 49))) + bonus 49 (HazardPattern.afterPattern 10000 p (.walk 49)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 49) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) < bonus 70 p at decreasing
  rw [gammaAfter106, at70] at decreasing
  have numeric := numeric106 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49))
  rw [oldBefore70, at70, literal, oldAfter106, gammaAfter106]
  exact numeric
theorem numeric107 (p : Pattern) (guard : d61360 p = 1) (decreasing : d2518 p < d3496 p) :
    d47866 p + d3496 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 70 p
  rw [at70] at beforeRange
  have afterRange := bonus_range 47 (HazardPattern.afterPattern 10000 p (.walk 47))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) ∧ bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) ≤ 2 at afterRange
  rw [gammaAfter107] at afterRange
  have possibilities : (d3496 p = 1 ∧ d2518 p = 0) ∨ (d3496 p = 2 ∧ d2518 p = 0) ∨ (d3496 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1978 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro5498 p guard beforeEq
    have complete := andIntro5519 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro5520 p guard beforeEq
    have complete := andIntro5541 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro5520 p guard beforeEq
    have complete := andIntro5562 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local107 (p : Pattern) (guard : d61360 p = 1)
    (decreasing : bonus 47 (HazardPattern.afterPattern 10000 p (.walk 47)) < bonus 70 p) :
    NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 70 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 47) + NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 47))) + bonus 47 (HazardPattern.afterPattern 10000 p (.walk 47)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 47) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) < bonus 70 p at decreasing
  rw [gammaAfter107, at70] at decreasing
  have numeric := numeric107 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47))
  rw [oldBefore70, at70, literal, oldAfter107, gammaAfter107]
  exact numeric
theorem numeric108 (p : Pattern) (guard : d73493 p = 1) (decreasing : d0 p < d3496 p) :
    d47866 p + d3496 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 70 p
  rw [at70] at beforeRange
  have afterRange := bonus_range 93 (HazardPattern.afterPattern 10000 p (.walk 93))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) ∧ bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) ≤ 2 at afterRange
  rw [gammaAfter108] at afterRange
  have possibilities : (d3496 p = 1 ∧ d0 p = 0) ∨ (d3496 p = 2 ∧ d0 p = 0) ∨ (d3496 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1978 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro5606 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4039 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro5627 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4040 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro5627 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4039 p complete
    omega
theorem local108 (p : Pattern) (guard : d73493 p = 1)
    (decreasing : bonus 93 (HazardPattern.afterPattern 10000 p (.walk 93)) < bonus 70 p) :
    NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 70 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 93) + NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 93))) + bonus 93 (HazardPattern.afterPattern 10000 p (.walk 93)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 93) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) < bonus 70 p at decreasing
  rw [gammaAfter108, at70] at decreasing
  have numeric := numeric108 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93))
  rw [oldBefore70, at70, literal, oldAfter108, gammaAfter108]
  exact numeric
theorem numeric109 (p : Pattern) (guard : d73495 p = 1) (decreasing : d5349 p < d3496 p) :
    d47866 p + d3496 p ≤ (0 : Int) + d47866 p + d5349 p := by
  have beforeRange := bonus_range 70 p
  rw [at70] at beforeRange
  have afterRange := bonus_range 91 (HazardPattern.afterPattern 10000 p (.walk 91))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) ∧ bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) ≤ 2 at afterRange
  rw [gammaAfter109] at afterRange
  have possibilities : (d3496 p = 1 ∧ d5349 p = 0) ∨ (d3496 p = 2 ∧ d5349 p = 0) ∨ (d3496 p = 2 ∧ d5349 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1978 p pair.1
    have afterEq := eqIntro2844 p pair.2
    have combined := andIntro5648 p beforeEq guard
    have complete := andIntro5669 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro2844 p pair.2
    have combined := andIntro5689 p beforeEq guard
    have complete := andIntro5710 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro3159 p pair.1
    have afterEq := eqIntro2893 p pair.2
    have combined := andIntro5689 p beforeEq guard
    have complete := andIntro5731 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local109 (p : Pattern) (guard : d73495 p = 1)
    (decreasing : bonus 91 (HazardPattern.afterPattern 10000 p (.walk 91)) < bonus 70 p) :
    NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 70 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 91) + NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 91))) + bonus 91 (HazardPattern.afterPattern 10000 p (.walk 91)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 91) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) < bonus 70 p at decreasing
  rw [gammaAfter109, at70] at decreasing
  have numeric := numeric109 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91))
  rw [oldBefore70, at70, literal, oldAfter109, gammaAfter109]
  exact numeric
theorem numeric110 (p : Pattern) (guard : d62934 p = 1) (decreasing : d2895 p < d3673 p) :
    d48087 p + d3673 p ≤ (0 : Int) + d48083 p + d2895 p := by
  have beforeRange := bonus_range 71 p
  rw [at71] at beforeRange
  have afterRange := bonus_range 49 (HazardPattern.afterPattern 10000 p (.walk 49))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) ∧ bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) ≤ 2 at afterRange
  rw [gammaAfter110] at afterRange
  have possibilities : (d3673 p = 1 ∧ d2895 p = 0) ∨ (d3673 p = 2 ∧ d2895 p = 0) ∨ (d3673 p = 2 ∧ d2895 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2106 p pair.1
    have afterEq := eqIntro1209 p pair.2
    have combined := andIntro5732 p beforeEq guard
    have complete := andIntro5780 p afterEq combined
    have bound := compare4041 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1209 p pair.2
    have combined := andIntro5781 p beforeEq guard
    have complete := andIntro5809 p afterEq combined
    have bound := compare4042 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1258 p pair.2
    have combined := andIntro5781 p beforeEq guard
    have complete := andIntro5837 p afterEq combined
    have bound := compare4041 p complete
    omega
theorem local110 (p : Pattern) (guard : d62934 p = 1)
    (decreasing : bonus 49 (HazardPattern.afterPattern 10000 p (.walk 49)) < bonus 71 p) :
    NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 71 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 49) + NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 49))) + bonus 49 (HazardPattern.afterPattern 10000 p (.walk 49)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 49) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) < bonus 71 p at decreasing
  rw [gammaAfter110, at71] at decreasing
  have numeric := numeric110 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49))
  rw [oldBefore71, at71, literal, oldAfter110, gammaAfter110]
  exact numeric
theorem numeric111 (p : Pattern) (guard : d54981 p = 1) (decreasing : d0 p < d3673 p) :
    d48087 p + d3673 p ≤ (1 : Int) + d47700 p + d0 p := by
  have beforeRange := bonus_range 71 p
  rw [at71] at beforeRange
  have afterRange := bonus_range 49 (HazardPattern.afterPattern 10000 p (.push 49 (.stay 27)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 49 (.stay 27))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 27))) ∧ bonus (HazardPattern.nextHero (.push 49 (.stay 27))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 27))) ≤ 2 at afterRange
  rw [gammaAfter111] at afterRange
  have possibilities : (d3673 p = 1 ∧ d0 p = 0) ∨ (d3673 p = 2 ∧ d0 p = 0) ∨ (d3673 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2106 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro5859 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4043 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro5880 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare4044 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro5880 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4043 p complete
    omega
theorem local111 (p : Pattern) (guard : d54981 p = 1)
    (decreasing : bonus 49 (HazardPattern.afterPattern 10000 p (.push 49 (.stay 27))) < bonus 71 p) :
    NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 71 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 49 (.stay 27)) + NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 49 (.stay 27)))) + bonus 49 (HazardPattern.afterPattern 10000 p (.push 49 (.stay 27))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 49 (.stay 27)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 49 (.stay 27))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 27))) < bonus 71 p at decreasing
  rw [gammaAfter111, at71] at decreasing
  have numeric := numeric111 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 49 (.stay 27))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 27)))
  rw [oldBefore71, at71, literal, oldAfter111, gammaAfter111]
  exact numeric
theorem numeric112 (p : Pattern) (guard : d73492 p = 1) (decreasing : d0 p < d3673 p) :
    d48087 p + d3673 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 71 p
  rw [at71] at beforeRange
  have afterRange := bonus_range 93 (HazardPattern.afterPattern 10000 p (.walk 93))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) ∧ bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) ≤ 2 at afterRange
  rw [gammaAfter112] at afterRange
  have possibilities : (d3673 p = 1 ∧ d0 p = 0) ∨ (d3673 p = 2 ∧ d0 p = 0) ∨ (d3673 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2106 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro5921 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4045 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro5942 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4046 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro5942 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4045 p complete
    omega
theorem local112 (p : Pattern) (guard : d73492 p = 1)
    (decreasing : bonus 93 (HazardPattern.afterPattern 10000 p (.walk 93)) < bonus 71 p) :
    NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 71 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 93) + NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 93))) + bonus 93 (HazardPattern.afterPattern 10000 p (.walk 93)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 93) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) < bonus 71 p at decreasing
  rw [gammaAfter112, at71] at decreasing
  have numeric := numeric112 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93))
  rw [oldBefore71, at71, literal, oldAfter112, gammaAfter112]
  exact numeric
theorem numeric113 (p : Pattern) (guard : d73777 p = 1) (decreasing : d0 p < d3673 p) :
    d48087 p + d3673 p ≤ (0 : Int) + d73782 p + d0 p := by
  have beforeRange := bonus_range 71 p
  rw [at71] at beforeRange
  have afterRange := bonus_range 93 (HazardPattern.afterPattern 10000 p (.push 93 (.stay 115)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 93 (.stay 115))) (HazardPattern.afterPattern 10000 p (.push 93 (.stay 115))) ∧ bonus (HazardPattern.nextHero (.push 93 (.stay 115))) (HazardPattern.afterPattern 10000 p (.push 93 (.stay 115))) ≤ 2 at afterRange
  rw [gammaAfter113] at afterRange
  have possibilities : (d3673 p = 1 ∧ d0 p = 0) ∨ (d3673 p = 2 ∧ d0 p = 0) ∨ (d3673 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2106 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6026 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4047 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6047 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4048 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6047 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4047 p complete
    omega
theorem local113 (p : Pattern) (guard : d73777 p = 1)
    (decreasing : bonus 93 (HazardPattern.afterPattern 10000 p (.push 93 (.stay 115))) < bonus 71 p) :
    NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 71 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 93 (.stay 115)) + NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 93 (.stay 115)))) + bonus 93 (HazardPattern.afterPattern 10000 p (.push 93 (.stay 115))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 93 (.stay 115)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 93 (.stay 115))) (HazardPattern.afterPattern 10000 p (.push 93 (.stay 115))) < bonus 71 p at decreasing
  rw [gammaAfter113, at71] at decreasing
  have numeric := numeric113 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 93 (.stay 115))) (HazardPattern.afterPattern 10000 p (.push 93 (.stay 115)))
  rw [oldBefore71, at71, literal, oldAfter113, gammaAfter113]
  exact numeric
theorem numeric114 (p : Pattern) (guard : d62374 p = 1) (decreasing : d3496 p < d3673 p) :
    d48087 p + d3673 p ≤ (0 : Int) + d47866 p + d3496 p := by
  have beforeRange := bonus_range 71 p
  rw [at71] at beforeRange
  have afterRange := bonus_range 70 (HazardPattern.afterPattern 10000 p (.walk 70))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ∧ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ≤ 2 at afterRange
  rw [gammaAfter114] at afterRange
  have possibilities : (d3673 p = 1 ∧ d3496 p = 0) ∨ (d3673 p = 2 ∧ d3496 p = 0) ∨ (d3673 p = 2 ∧ d3496 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2106 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro6069 p guard beforeEq
    have complete := andIntro6090 p afterEq combined
    have bound := compare4049 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro6111 p guard beforeEq
    have complete := andIntro6112 p combined afterEq
    have bound := compare4050 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1978 p pair.2
    have combined := andIntro6111 p guard beforeEq
    have complete := andIntro6113 p combined afterEq
    have bound := compare4049 p complete
    omega
theorem local114 (p : Pattern) (guard : d62374 p = 1)
    (decreasing : bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 71 p) :
    NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 71 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 70) + NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 70))) + bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 70) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 71 p at decreasing
  rw [gammaAfter114, at71] at decreasing
  have numeric := numeric114 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70))
  rw [oldBefore71, at71, literal, oldAfter114, gammaAfter114]
  exact numeric
theorem numeric115 (p : Pattern) (guard : d72603 p = 1) (decreasing : d73909 p < d3673 p) :
    d48087 p + d3673 p ≤ (1 : Int) + d47866 p + d73909 p := by
  have beforeRange := bonus_range 71 p
  rw [at71] at beforeRange
  have afterRange := bonus_range 70 (HazardPattern.afterPattern 10000 p (.push 70 (.stay 69)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 70 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 70 (.stay 69))) ∧ bonus (HazardPattern.nextHero (.push 70 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 70 (.stay 69))) ≤ 2 at afterRange
  rw [gammaAfter115] at afterRange
  have possibilities : (d3673 p = 1 ∧ d73909 p = 0) ∨ (d3673 p = 2 ∧ d73909 p = 0) ∨ (d3673 p = 2 ∧ d73909 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2106 p pair.1
    have afterEq := eqIntro3215 p pair.2
    have combined := andIntro6134 p beforeEq guard
    have complete := andIntro6135 p combined afterEq
    have bound := compare4242 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro3215 p pair.2
    have combined := andIntro6136 p beforeEq guard
    have complete := andIntro6157 p combined afterEq
    have bound := compare4049 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro3216 p pair.2
    have combined := andIntro6136 p beforeEq guard
    have complete := andIntro6158 p combined afterEq
    have bound := compare4369 p complete
    omega
theorem local115 (p : Pattern) (guard : d72603 p = 1)
    (decreasing : bonus 70 (HazardPattern.afterPattern 10000 p (.push 70 (.stay 69))) < bonus 71 p) :
    NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 71 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 70 (.stay 69)) + NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 70 (.stay 69)))) + bonus 70 (HazardPattern.afterPattern 10000 p (.push 70 (.stay 69))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 70 (.stay 69)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 70 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 70 (.stay 69))) < bonus 71 p at decreasing
  rw [gammaAfter115, at71] at decreasing
  have numeric := numeric115 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 70 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 70 (.stay 69)))
  rw [oldBefore71, at71, literal, oldAfter115, gammaAfter115]
  exact numeric
theorem numeric116 (p : Pattern) (guard : d64965 p = 1) (decreasing : d3015 p < d3673 p) :
    d48087 p + d3673 p ≤ (0 : Int) + d47911 p + d3015 p := by
  have beforeRange := bonus_range 71 p
  rw [at71] at beforeRange
  have afterRange := bonus_range 50 (HazardPattern.afterPattern 10000 p (.walk 50))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ∧ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ≤ 2 at afterRange
  rw [gammaAfter116] at afterRange
  have possibilities : (d3673 p = 1 ∧ d3015 p = 0) ∨ (d3673 p = 2 ∧ d3015 p = 0) ∨ (d3673 p = 2 ∧ d3015 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2106 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro6180 p beforeEq guard
    have complete := andIntro6201 p afterEq combined
    have bound := compare4045 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro6222 p beforeEq guard
    have complete := andIntro834 p combined afterEq
    have bound := compare4046 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1406 p pair.2
    have combined := andIntro6222 p beforeEq guard
    have complete := andIntro835 p combined afterEq
    have bound := compare4045 p complete
    omega
theorem local116 (p : Pattern) (guard : d64965 p = 1)
    (decreasing : bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 71 p) :
    NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 71 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 50) + NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 50))) + bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 50) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 71 p at decreasing
  rw [gammaAfter116, at71] at decreasing
  have numeric := numeric116 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50))
  rw [oldBefore71, at71, literal, oldAfter116, gammaAfter116]
  exact numeric
theorem numeric117 (p : Pattern) (guard : d62376 p = 1) (decreasing : d2782 p < d3673 p) :
    d48087 p + d3673 p ≤ (0 : Int) + d48080 p + d2782 p := by
  have beforeRange := bonus_range 71 p
  rw [at71] at beforeRange
  have afterRange := bonus_range 48 (HazardPattern.afterPattern 10000 p (.walk 48))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ∧ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ≤ 2 at afterRange
  rw [gammaAfter117] at afterRange
  have possibilities : (d3673 p = 1 ∧ d2782 p = 0) ∨ (d3673 p = 2 ∧ d2782 p = 0) ∨ (d3673 p = 2 ∧ d2782 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2106 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro6223 p guard beforeEq
    have complete := andIntro6245 p afterEq combined
    have bound := compare4370 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro6246 p guard beforeEq
    have complete := andIntro6267 p afterEq combined
    have bound := compare4371 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1166 p pair.2
    have combined := andIntro6246 p guard beforeEq
    have complete := andIntro6288 p afterEq combined
    have bound := compare4370 p complete
    omega
theorem local117 (p : Pattern) (guard : d62376 p = 1)
    (decreasing : bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 71 p) :
    NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 71 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 48) + NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 48))) + bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 48) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 71 p at decreasing
  rw [gammaAfter117, at71] at decreasing
  have numeric := numeric117 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48))
  rw [oldBefore71, at71, literal, oldAfter117, gammaAfter117]
  exact numeric
theorem numeric118 (p : Pattern) (guard : d74039 p = 1) (decreasing : d0 p < d3673 p) :
    d48087 p + d3673 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 71 p
  rw [at71] at beforeRange
  have afterRange := bonus_range 94 (HazardPattern.afterPattern 10000 p (.walk 94))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) ∧ bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) ≤ 2 at afterRange
  rw [gammaAfter118] at afterRange
  have possibilities : (d3673 p = 1 ∧ d0 p = 0) ∨ (d3673 p = 2 ∧ d0 p = 0) ∨ (d3673 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2106 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6290 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4045 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6292 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare4046 p complete
    omega
  · have beforeEq := eqIntro3194 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6292 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare4045 p complete
    omega
theorem local118 (p : Pattern) (guard : d74039 p = 1)
    (decreasing : bonus 94 (HazardPattern.afterPattern 10000 p (.walk 94)) < bonus 71 p) :
    NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 71 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 94) + NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 94))) + bonus 94 (HazardPattern.afterPattern 10000 p (.walk 94)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 94) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) < bonus 71 p at decreasing
  rw [gammaAfter118, at71] at decreasing
  have numeric := numeric118 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94))
  rw [oldBefore71, at71, literal, oldAfter118, gammaAfter118]
  exact numeric
theorem numeric119 (p : Pattern) (guard : d64793 p = 1) (decreasing : d3142 p < d3842 p) :
    d47911 p + d3842 p ≤ (0 : Int) + d47911 p + d3142 p := by
  have beforeRange := bonus_range 73 p
  rw [at73] at beforeRange
  have afterRange := bonus_range 51 (HazardPattern.afterPattern 10000 p (.walk 51))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ∧ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ≤ 2 at afterRange
  rw [gammaAfter119] at afterRange
  have possibilities : (d3842 p = 1 ∧ d3142 p = 0) ∨ (d3842 p = 2 ∧ d3142 p = 0) ∨ (d3842 p = 2 ∧ d3142 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2342 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro6293 p beforeEq guard
    have complete := andIntro6328 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro6329 p beforeEq guard
    have complete := andIntro2752 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1448 p pair.2
    have combined := andIntro6329 p beforeEq guard
    have complete := andIntro2753 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local119 (p : Pattern) (guard : d64793 p = 1)
    (decreasing : bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 73 p) :
    NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 73 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 51) + NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 51))) + bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 51) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 73 p at decreasing
  rw [gammaAfter119, at73] at decreasing
  have numeric := numeric119 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51))
  rw [oldBefore73, at73, literal, oldAfter119, gammaAfter119]
  exact numeric
theorem numeric120 (p : Pattern) (guard : d56153 p = 1) (decreasing : d0 p < d3842 p) :
    d47911 p + d3842 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 73 p
  rw [at73] at beforeRange
  have afterRange := bonus_range 51 (HazardPattern.afterPattern 10000 p (.push 51 (.stay 29)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 51 (.stay 29))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 29))) ∧ bonus (HazardPattern.nextHero (.push 51 (.stay 29))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 29))) ≤ 2 at afterRange
  rw [gammaAfter120] at afterRange
  have possibilities : (d3842 p = 1 ∧ d0 p = 0) ∨ (d3842 p = 2 ∧ d0 p = 0) ∨ (d3842 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2342 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6350 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6351 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6351 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local120 (p : Pattern) (guard : d56153 p = 1)
    (decreasing : bonus 51 (HazardPattern.afterPattern 10000 p (.push 51 (.stay 29))) < bonus 73 p) :
    NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 73 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 51 (.stay 29)) + NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 51 (.stay 29)))) + bonus 51 (HazardPattern.afterPattern 10000 p (.push 51 (.stay 29))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 51 (.stay 29)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 51 (.stay 29))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 29))) < bonus 73 p at decreasing
  rw [gammaAfter120, at73] at decreasing
  have numeric := numeric120 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 51 (.stay 29))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 29)))
  rw [oldBefore73, at73, literal, oldAfter120, gammaAfter120]
  exact numeric
theorem numeric121 (p : Pattern) (guard : d74040 p = 1) (decreasing : d0 p < d3842 p) :
    d47911 p + d3842 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 73 p
  rw [at73] at beforeRange
  have afterRange := bonus_range 95 (HazardPattern.afterPattern 10000 p (.walk 95))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) ∧ bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) ≤ 2 at afterRange
  rw [gammaAfter121] at afterRange
  have possibilities : (d3842 p = 1 ∧ d0 p = 0) ∨ (d3842 p = 2 ∧ d0 p = 0) ∨ (d3842 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2342 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6410 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6411 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6411 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local121 (p : Pattern) (guard : d74040 p = 1)
    (decreasing : bonus 95 (HazardPattern.afterPattern 10000 p (.walk 95)) < bonus 73 p) :
    NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 73 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 95) + NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 95))) + bonus 95 (HazardPattern.afterPattern 10000 p (.walk 95)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 95) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) < bonus 73 p at decreasing
  rw [gammaAfter121, at73] at decreasing
  have numeric := numeric121 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95))
  rw [oldBefore73, at73, literal, oldAfter121, gammaAfter121]
  exact numeric
theorem numeric122 (p : Pattern) (guard : d66089 p = 1) (decreasing : d4025 p < d3842 p) :
    d47911 p + d3842 p ≤ (0 : Int) + d47911 p + d4025 p := by
  have beforeRange := bonus_range 73 p
  rw [at73] at beforeRange
  have afterRange := bonus_range 74 (HazardPattern.afterPattern 10000 p (.walk 74))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) ∧ bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) ≤ 2 at afterRange
  rw [gammaAfter122] at afterRange
  have possibilities : (d3842 p = 1 ∧ d4025 p = 0) ∨ (d3842 p = 2 ∧ d4025 p = 0) ∨ (d3842 p = 2 ∧ d4025 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2342 p pair.1
    have afterEq := eqIntro2480 p pair.2
    have combined := andIntro6446 p beforeEq guard
    have complete := andIntro3414 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro2480 p pair.2
    have combined := andIntro6447 p beforeEq guard
    have complete := andIntro3414 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro2481 p pair.2
    have combined := andIntro6447 p beforeEq guard
    have complete := andIntro3415 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local122 (p : Pattern) (guard : d66089 p = 1)
    (decreasing : bonus 74 (HazardPattern.afterPattern 10000 p (.walk 74)) < bonus 73 p) :
    NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 73 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 74) + NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 74))) + bonus 74 (HazardPattern.afterPattern 10000 p (.walk 74)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 74) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) < bonus 73 p at decreasing
  rw [gammaAfter122, at73] at decreasing
  have numeric := numeric122 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74))
  rw [oldBefore73, at73, literal, oldAfter122, gammaAfter122]
  exact numeric
theorem numeric123 (p : Pattern) (guard : d67300 p = 1) (decreasing : d2671 p < d3842 p) :
    d47911 p + d3842 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 73 p
  rw [at73] at beforeRange
  have afterRange := bonus_range 52 (HazardPattern.afterPattern 10000 p (.walk 52))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) ∧ bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) ≤ 2 at afterRange
  rw [gammaAfter123] at afterRange
  have possibilities : (d3842 p = 1 ∧ d2671 p = 0) ∨ (d3842 p = 2 ∧ d2671 p = 0) ∨ (d3842 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2342 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro6448 p beforeEq guard
    have complete := andIntro6469 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro6470 p beforeEq guard
    have complete := andIntro2707 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro6470 p beforeEq guard
    have complete := andIntro2708 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local123 (p : Pattern) (guard : d67300 p = 1)
    (decreasing : bonus 52 (HazardPattern.afterPattern 10000 p (.walk 52)) < bonus 73 p) :
    NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 73 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 52) + NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 52))) + bonus 52 (HazardPattern.afterPattern 10000 p (.walk 52)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 52) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) < bonus 73 p at decreasing
  rw [gammaAfter123, at73] at decreasing
  have numeric := numeric123 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52))
  rw [oldBefore73, at73, literal, oldAfter123, gammaAfter123]
  exact numeric
theorem numeric124 (p : Pattern) (guard : d64794 p = 1) (decreasing : d3015 p < d3842 p) :
    d47911 p + d3842 p ≤ (0 : Int) + d47911 p + d3015 p := by
  have beforeRange := bonus_range 73 p
  rw [at73] at beforeRange
  have afterRange := bonus_range 50 (HazardPattern.afterPattern 10000 p (.walk 50))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ∧ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ≤ 2 at afterRange
  rw [gammaAfter124] at afterRange
  have possibilities : (d3842 p = 1 ∧ d3015 p = 0) ∨ (d3842 p = 2 ∧ d3015 p = 0) ∨ (d3842 p = 2 ∧ d3015 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2342 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro6491 p beforeEq guard
    have complete := andIntro834 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro2878 p beforeEq guard
    have complete := andIntro834 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1406 p pair.2
    have combined := andIntro2878 p beforeEq guard
    have complete := andIntro835 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local124 (p : Pattern) (guard : d64794 p = 1)
    (decreasing : bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 73 p) :
    NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 73 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 50) + NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 50))) + bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 50) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 73 p at decreasing
  rw [gammaAfter124, at73] at decreasing
  have numeric := numeric124 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50))
  rw [oldBefore73, at73, literal, oldAfter124, gammaAfter124]
  exact numeric
theorem numeric125 (p : Pattern) (guard : d74046 p = 1) (decreasing : d0 p < d3842 p) :
    d47911 p + d3842 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 73 p
  rw [at73] at beforeRange
  have afterRange := bonus_range 96 (HazardPattern.afterPattern 10000 p (.walk 96))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) ∧ bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) ≤ 2 at afterRange
  rw [gammaAfter125] at afterRange
  have possibilities : (d3842 p = 1 ∧ d0 p = 0) ∨ (d3842 p = 2 ∧ d0 p = 0) ∨ (d3842 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2342 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6550 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6551 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6551 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local125 (p : Pattern) (guard : d74046 p = 1)
    (decreasing : bonus 96 (HazardPattern.afterPattern 10000 p (.walk 96)) < bonus 73 p) :
    NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 73 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 96) + NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 96))) + bonus 96 (HazardPattern.afterPattern 10000 p (.walk 96)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 96) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) < bonus 73 p at decreasing
  rw [gammaAfter125, at73] at decreasing
  have numeric := numeric125 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96))
  rw [oldBefore73, at73, literal, oldAfter125, gammaAfter125]
  exact numeric
theorem numeric126 (p : Pattern) (guard : d74047 p = 1) (decreasing : d0 p < d3842 p) :
    d47911 p + d3842 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 73 p
  rw [at73] at beforeRange
  have afterRange := bonus_range 94 (HazardPattern.afterPattern 10000 p (.walk 94))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) ∧ bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) ≤ 2 at afterRange
  rw [gammaAfter126] at afterRange
  have possibilities : (d3842 p = 1 ∧ d0 p = 0) ∨ (d3842 p = 2 ∧ d0 p = 0) ∨ (d3842 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2342 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6553 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6554 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3251 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6554 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local126 (p : Pattern) (guard : d74047 p = 1)
    (decreasing : bonus 94 (HazardPattern.afterPattern 10000 p (.walk 94)) < bonus 73 p) :
    NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 73 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 94) + NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 94))) + bonus 94 (HazardPattern.afterPattern 10000 p (.walk 94)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 94) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) < bonus 73 p at decreasing
  rw [gammaAfter126, at73] at decreasing
  have numeric := numeric126 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94))
  rw [oldBefore73, at73, literal, oldAfter126, gammaAfter126]
  exact numeric
theorem numeric127 (p : Pattern) (guard : d66275 p = 1) (decreasing : d2671 p < d4025 p) :
    d47911 p + d4025 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 74 p
  rw [at74] at beforeRange
  have afterRange := bonus_range 52 (HazardPattern.afterPattern 10000 p (.walk 52))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) ∧ bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) ≤ 2 at afterRange
  rw [gammaAfter127] at afterRange
  have possibilities : (d4025 p = 1 ∧ d2671 p = 0) ∨ (d4025 p = 2 ∧ d2671 p = 0) ∨ (d4025 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2481 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro6555 p beforeEq guard
    have complete := andIntro6590 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro6591 p beforeEq guard
    have complete := andIntro2707 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro6591 p beforeEq guard
    have complete := andIntro2708 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local127 (p : Pattern) (guard : d66275 p = 1)
    (decreasing : bonus 52 (HazardPattern.afterPattern 10000 p (.walk 52)) < bonus 74 p) :
    NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 74 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 52) + NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 52))) + bonus 52 (HazardPattern.afterPattern 10000 p (.walk 52)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 52) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) < bonus 74 p at decreasing
  rw [gammaAfter127, at74] at decreasing
  have numeric := numeric127 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52))
  rw [oldBefore74, at74, literal, oldAfter127, gammaAfter127]
  exact numeric
theorem numeric128 (p : Pattern) (guard : d56776 p = 1) (decreasing : d0 p < d4025 p) :
    d47911 p + d4025 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 74 p
  rw [at74] at beforeRange
  have afterRange := bonus_range 52 (HazardPattern.afterPattern 10000 p (.push 52 (.stay 30)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 52 (.stay 30))) (HazardPattern.afterPattern 10000 p (.push 52 (.stay 30))) ∧ bonus (HazardPattern.nextHero (.push 52 (.stay 30))) (HazardPattern.afterPattern 10000 p (.push 52 (.stay 30))) ≤ 2 at afterRange
  rw [gammaAfter128] at afterRange
  have possibilities : (d4025 p = 1 ∧ d0 p = 0) ∨ (d4025 p = 2 ∧ d0 p = 0) ∨ (d4025 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2481 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6593 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6594 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6594 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local128 (p : Pattern) (guard : d56776 p = 1)
    (decreasing : bonus 52 (HazardPattern.afterPattern 10000 p (.push 52 (.stay 30))) < bonus 74 p) :
    NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 74 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 52 (.stay 30)) + NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 52 (.stay 30)))) + bonus 52 (HazardPattern.afterPattern 10000 p (.push 52 (.stay 30))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 52 (.stay 30)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 52 (.stay 30))) (HazardPattern.afterPattern 10000 p (.push 52 (.stay 30))) < bonus 74 p at decreasing
  rw [gammaAfter128, at74] at decreasing
  have numeric := numeric128 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 52 (.stay 30))) (HazardPattern.afterPattern 10000 p (.push 52 (.stay 30)))
  rw [oldBefore74, at74, literal, oldAfter128, gammaAfter128]
  exact numeric
theorem numeric129 (p : Pattern) (guard : d74048 p = 1) (decreasing : d0 p < d4025 p) :
    d47911 p + d4025 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 74 p
  rw [at74] at beforeRange
  have afterRange := bonus_range 96 (HazardPattern.afterPattern 10000 p (.walk 96))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) ∧ bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) ≤ 2 at afterRange
  rw [gammaAfter129] at afterRange
  have possibilities : (d4025 p = 1 ∧ d0 p = 0) ∨ (d4025 p = 2 ∧ d0 p = 0) ∨ (d4025 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2481 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6653 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6654 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6654 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local129 (p : Pattern) (guard : d74048 p = 1)
    (decreasing : bonus 96 (HazardPattern.afterPattern 10000 p (.walk 96)) < bonus 74 p) :
    NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 74 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 96) + NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 96))) + bonus 96 (HazardPattern.afterPattern 10000 p (.walk 96)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 96) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) < bonus 74 p at decreasing
  rw [gammaAfter129, at74] at decreasing
  have numeric := numeric129 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96))
  rw [oldBefore74, at74, literal, oldAfter129, gammaAfter129]
  exact numeric
theorem numeric130 (p : Pattern) (guard : d74052 p = 1) (decreasing : d0 p < d4025 p) :
    d47911 p + d4025 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 74 p
  rw [at74] at beforeRange
  have afterRange := bonus_range 96 (HazardPattern.afterPattern 10000 p (.push 96 (.stay 118)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 96 (.stay 118))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 118))) ∧ bonus (HazardPattern.nextHero (.push 96 (.stay 118))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 118))) ≤ 2 at afterRange
  rw [gammaAfter130] at afterRange
  have possibilities : (d4025 p = 1 ∧ d0 p = 0) ∨ (d4025 p = 2 ∧ d0 p = 0) ∨ (d4025 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2481 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6655 p beforeEq guard
    have complete := andIntro6656 p afterEq combined
    have bound := compare4372 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6657 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6657 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local130 (p : Pattern) (guard : d74052 p = 1)
    (decreasing : bonus 96 (HazardPattern.afterPattern 10000 p (.push 96 (.stay 118))) < bonus 74 p) :
    NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 74 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 96 (.stay 118)) + NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 96 (.stay 118)))) + bonus 96 (HazardPattern.afterPattern 10000 p (.push 96 (.stay 118))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 96 (.stay 118)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 96 (.stay 118))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 118))) < bonus 74 p at decreasing
  rw [gammaAfter130, at74] at decreasing
  have numeric := numeric130 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 96 (.stay 118))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 118)))
  rw [oldBefore74, at74, literal, oldAfter130, gammaAfter130]
  exact numeric
theorem numeric131 (p : Pattern) (guard : d66089 p = 1) (decreasing : d3842 p < d4025 p) :
    d47911 p + d4025 p ≤ (0 : Int) + d47911 p + d3842 p := by
  have beforeRange := bonus_range 74 p
  rw [at74] at beforeRange
  have afterRange := bonus_range 73 (HazardPattern.afterPattern 10000 p (.walk 73))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ∧ bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) ≤ 2 at afterRange
  rw [gammaAfter131] at afterRange
  have possibilities : (d4025 p = 1 ∧ d3842 p = 0) ∨ (d4025 p = 2 ∧ d3842 p = 0) ∨ (d4025 p = 2 ∧ d3842 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2481 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro6692 p beforeEq guard
    have complete := andIntro2877 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro2341 p pair.2
    have combined := andIntro6447 p beforeEq guard
    have complete := andIntro2877 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro2342 p pair.2
    have combined := andIntro6447 p beforeEq guard
    have complete := andIntro2879 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local131 (p : Pattern) (guard : d66089 p = 1)
    (decreasing : bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 74 p) :
    NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 74 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 73) + NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 73))) + bonus 73 (HazardPattern.afterPattern 10000 p (.walk 73)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 73) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) < bonus 74 p at decreasing
  rw [gammaAfter131, at74] at decreasing
  have numeric := numeric131 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73))
  rw [oldBefore74, at74, literal, oldAfter131, gammaAfter131]
  exact numeric
theorem numeric132 (p : Pattern) (guard : d66091 p = 1) (decreasing : d3142 p < d4025 p) :
    d47911 p + d4025 p ≤ (0 : Int) + d47911 p + d3142 p := by
  have beforeRange := bonus_range 74 p
  rw [at74] at beforeRange
  have afterRange := bonus_range 51 (HazardPattern.afterPattern 10000 p (.walk 51))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ∧ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ≤ 2 at afterRange
  rw [gammaAfter132] at afterRange
  have possibilities : (d4025 p = 1 ∧ d3142 p = 0) ∨ (d4025 p = 2 ∧ d3142 p = 0) ∨ (d4025 p = 2 ∧ d3142 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2481 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro6693 p beforeEq guard
    have complete := andIntro6714 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro6715 p beforeEq guard
    have complete := andIntro2752 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1448 p pair.2
    have combined := andIntro6715 p beforeEq guard
    have complete := andIntro2753 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local132 (p : Pattern) (guard : d66091 p = 1)
    (decreasing : bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 74 p) :
    NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 74 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 51) + NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 51))) + bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 51) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 74 p at decreasing
  rw [gammaAfter132, at74] at decreasing
  have numeric := numeric132 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51))
  rw [oldBefore74, at74, literal, oldAfter132, gammaAfter132]
  exact numeric
theorem numeric133 (p : Pattern) (guard : d74056 p = 1) (decreasing : d0 p < d4025 p) :
    d47911 p + d4025 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 74 p
  rw [at74] at beforeRange
  have afterRange := bonus_range 97 (HazardPattern.afterPattern 10000 p (.walk 97))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ∧ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ≤ 2 at afterRange
  rw [gammaAfter133] at afterRange
  have possibilities : (d4025 p = 1 ∧ d0 p = 0) ∨ (d4025 p = 2 ∧ d0 p = 0) ∨ (d4025 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2481 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6718 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6719 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6719 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local133 (p : Pattern) (guard : d74056 p = 1)
    (decreasing : bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 74 p) :
    NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 74 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 97) + NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 97))) + bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 97) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 74 p at decreasing
  rw [gammaAfter133, at74] at decreasing
  have numeric := numeric133 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97))
  rw [oldBefore74, at74, literal, oldAfter133, gammaAfter133]
  exact numeric
theorem numeric134 (p : Pattern) (guard : d74062 p = 1) (decreasing : d0 p < d4025 p) :
    d47911 p + d4025 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 74 p
  rw [at74] at beforeRange
  have afterRange := bonus_range 95 (HazardPattern.afterPattern 10000 p (.walk 95))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) ∧ bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) ≤ 2 at afterRange
  rw [gammaAfter134] at afterRange
  have possibilities : (d4025 p = 1 ∧ d0 p = 0) ∨ (d4025 p = 2 ∧ d0 p = 0) ∨ (d4025 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro2481 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6778 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro6779 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro3286 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro6779 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare9 p complete
    omega
theorem local134 (p : Pattern) (guard : d74062 p = 1)
    (decreasing : bonus 95 (HazardPattern.afterPattern 10000 p (.walk 95)) < bonus 74 p) :
    NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 74 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 95) + NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 95))) + bonus 95 (HazardPattern.afterPattern 10000 p (.walk 95)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 95) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) < bonus 74 p at decreasing
  rw [gammaAfter134, at74] at decreasing
  have numeric := numeric134 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95))
  rw [oldBefore74, at74, literal, oldAfter134, gammaAfter134]
  exact numeric
theorem numeric135 (p : Pattern) (guard : d74067 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 76 p
  rw [at76] at beforeRange
  have afterRange := bonus_range 98 (HazardPattern.afterPattern 10000 p (.walk 98))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) ∧ bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) ≤ 2 at afterRange
  rw [gammaAfter135] at afterRange
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
theorem local135 (p : Pattern) (guard : d74067 p = 1)
    (decreasing : bonus 98 (HazardPattern.afterPattern 10000 p (.walk 98)) < bonus 76 p) :
    NetHack.Sokoban22Refined85.bonus 76 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 76 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 98) + NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 98))) + bonus 98 (HazardPattern.afterPattern 10000 p (.walk 98)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 98) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) < bonus 76 p at decreasing
  rw [gammaAfter135, at76] at decreasing
  have numeric := numeric135 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98))
  rw [oldBefore76, at76, literal, oldAfter135, gammaAfter135]
  exact numeric
theorem numeric136 (p : Pattern) (guard : d74072 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 76 p
  rw [at76] at beforeRange
  have afterRange := bonus_range 98 (HazardPattern.afterPattern 10000 p (.push 98 (.stay 120)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 98 (.stay 120))) (HazardPattern.afterPattern 10000 p (.push 98 (.stay 120))) ∧ bonus (HazardPattern.nextHero (.push 98 (.stay 120))) (HazardPattern.afterPattern 10000 p (.push 98 (.stay 120))) ≤ 2 at afterRange
  rw [gammaAfter136] at afterRange
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
theorem local136 (p : Pattern) (guard : d74072 p = 1)
    (decreasing : bonus 98 (HazardPattern.afterPattern 10000 p (.push 98 (.stay 120))) < bonus 76 p) :
    NetHack.Sokoban22Refined85.bonus 76 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 76 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 98 (.stay 120)) + NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 98 (.stay 120)))) + bonus 98 (HazardPattern.afterPattern 10000 p (.push 98 (.stay 120))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 98 (.stay 120)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 98 (.stay 120))) (HazardPattern.afterPattern 10000 p (.push 98 (.stay 120))) < bonus 76 p at decreasing
  rw [gammaAfter136, at76] at decreasing
  have numeric := numeric136 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 98 (.stay 120))) (HazardPattern.afterPattern 10000 p (.push 98 (.stay 120)))
  rw [oldBefore76, at76, literal, oldAfter136, gammaAfter136]
  exact numeric
theorem numeric137 (p : Pattern) (guard : d74074 p = 1) (decreasing : d0 p < d0 p) :
    d47911 p + d0 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 76 p
  rw [at76] at beforeRange
  have afterRange := bonus_range 97 (HazardPattern.afterPattern 10000 p (.walk 97))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ∧ bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) ≤ 2 at afterRange
  rw [gammaAfter137] at afterRange
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
theorem local137 (p : Pattern) (guard : d74074 p = 1)
    (decreasing : bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 76 p) :
    NetHack.Sokoban22Refined85.bonus 76 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 76 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 97) + NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 97))) + bonus 97 (HazardPattern.afterPattern 10000 p (.walk 97)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 97) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) < bonus 76 p at decreasing
  rw [gammaAfter137, at76] at decreasing
  have numeric := numeric137 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97))
  rw [oldBefore76, at76, literal, oldAfter137, gammaAfter137]
  exact numeric
theorem numeric138 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 78 p
  rw [at78] at beforeRange
  have afterRange := bonus_range 100 (HazardPattern.afterPattern 10000 p (.walk 100))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) ∧ bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) ≤ 2 at afterRange
  rw [gammaAfter138] at afterRange
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
theorem local138 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 100 (HazardPattern.afterPattern 10000 p (.walk 100)) < bonus 78 p) :
    NetHack.Sokoban22Refined85.bonus 78 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 78 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 100) + NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 100))) + bonus 100 (HazardPattern.afterPattern 10000 p (.walk 100)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 100) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) < bonus 78 p at decreasing
  rw [gammaAfter138, at78] at decreasing
  have numeric := numeric138 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100))
  rw [oldBefore78, at78, literal, oldAfter138, gammaAfter138]
  exact numeric
theorem numeric139 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 78 p
  rw [at78] at beforeRange
  have afterRange := bonus_range 100 (HazardPattern.afterPattern 10000 p (.push 100 (.stay 122)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 100 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 100 (.stay 122))) ∧ bonus (HazardPattern.nextHero (.push 100 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 100 (.stay 122))) ≤ 2 at afterRange
  rw [gammaAfter139] at afterRange
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
theorem local139 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 100 (HazardPattern.afterPattern 10000 p (.push 100 (.stay 122))) < bonus 78 p) :
    NetHack.Sokoban22Refined85.bonus 78 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 78 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 100 (.stay 122)) + NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 100 (.stay 122)))) + bonus 100 (HazardPattern.afterPattern 10000 p (.push 100 (.stay 122))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 100 (.stay 122)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 100 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 100 (.stay 122))) < bonus 78 p at decreasing
  rw [gammaAfter139, at78] at decreasing
  have numeric := numeric139 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 100 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 100 (.stay 122)))
  rw [oldBefore78, at78, literal, oldAfter139, gammaAfter139]
  exact numeric
end NetHack.Soko22Hazard87
