import NetHack.Soko22Hazard87.Numeric006
import NetHack.Soko22Hazard87.AndIntroBlocks0096
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric490 (p : Pattern) (guard : d100900 p = 1) (decreasing : d0 p < d0 p) :
    d48251 p + d0 p ≤ (0 : Int) + d48097 p + d0 p := by
  have beforeRange := bonus_range 138 p
  rw [at138] at beforeRange
  have afterRange := bonus_range 115 (HazardPattern.afterPattern 10000 p (.walk 115))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) ∧ bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) ≤ 2 at afterRange
  rw [gammaAfter490] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14399 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10077 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro14399 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10078 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro14399 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10077 p complete
    omega
theorem local490 (p : Pattern) (guard : d100900 p = 1)
    (decreasing : bonus 115 (HazardPattern.afterPattern 10000 p (.walk 115)) < bonus 138 p) :
    NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 138 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 115) + NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 115))) + bonus 115 (HazardPattern.afterPattern 10000 p (.walk 115)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 115) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) < bonus 138 p at decreasing
  rw [gammaAfter490, at138] at decreasing
  have numeric := numeric490 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115))
  rw [oldBefore138, at138, literal, oldAfter490, gammaAfter490]
  exact numeric
theorem numeric491 (p : Pattern) (guard : d128580 p = 1) (decreasing : d18533 p < d0 p) :
    d48251 p + d0 p ≤ (0 : Int) + d48547 p + d18533 p := by
  have beforeRange := bonus_range 138 p
  rw [at138] at beforeRange
  have afterRange := bonus_range 161 (HazardPattern.afterPattern 10000 p (.walk 161))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) ∧ bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) ≤ 2 at afterRange
  rw [gammaAfter491] at afterRange
  have possibilities : (d0 p = 1 ∧ d18533 p = 0) ∨ (d0 p = 2 ∧ d18533 p = 0) ∨ (d0 p = 2 ∧ d18533 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro10408 p pair.2
    have combined := andIntro23124 p beforeEq guard
    have complete := andIntro23125 p combined afterEq
    have bound := compare10079 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro10408 p pair.2
    have combined := andIntro23124 p beforeEq guard
    have complete := andIntro23125 p combined afterEq
    have bound := compare10080 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro10478 p pair.2
    have combined := andIntro23124 p beforeEq guard
    have complete := andIntro23126 p combined afterEq
    have bound := compare10079 p complete
    omega
theorem local491 (p : Pattern) (guard : d128580 p = 1)
    (decreasing : bonus 161 (HazardPattern.afterPattern 10000 p (.walk 161)) < bonus 138 p) :
    NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 138 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 161) + NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 161))) + bonus 161 (HazardPattern.afterPattern 10000 p (.walk 161)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 161) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) < bonus 138 p at decreasing
  rw [gammaAfter491, at138] at decreasing
  have numeric := numeric491 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161))
  rw [oldBefore138, at138, literal, oldAfter491, gammaAfter491]
  exact numeric
theorem numeric492 (p : Pattern) (guard : d129472 p = 1) (decreasing : d15965 p < d0 p) :
    d48251 p + d0 p ≤ (0 : Int) + d47866 p + d15965 p := by
  have beforeRange := bonus_range 138 p
  rw [at138] at beforeRange
  have afterRange := bonus_range 159 (HazardPattern.afterPattern 10000 p (.walk 159))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ∧ bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) ≤ 2 at afterRange
  rw [gammaAfter492] at afterRange
  have possibilities : (d0 p = 1 ∧ d15965 p = 0) ∨ (d0 p = 2 ∧ d15965 p = 0) ∨ (d0 p = 2 ∧ d15965 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro23127 p beforeEq guard
    have complete := andIntro23128 p combined afterEq
    have bound := compare10081 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro9726 p pair.2
    have combined := andIntro23127 p beforeEq guard
    have complete := andIntro23128 p combined afterEq
    have bound := compare10082 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro9862 p pair.2
    have combined := andIntro23127 p beforeEq guard
    have complete := andIntro23129 p combined afterEq
    have bound := compare10081 p complete
    omega
theorem local492 (p : Pattern) (guard : d129472 p = 1)
    (decreasing : bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 138 p) :
    NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 138 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 159) + NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 159))) + bonus 159 (HazardPattern.afterPattern 10000 p (.walk 159)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 159) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) < bonus 138 p at decreasing
  rw [gammaAfter492, at138] at decreasing
  have numeric := numeric492 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159))
  rw [oldBefore138, at138, literal, oldAfter492, gammaAfter492]
  exact numeric
theorem numeric493 (p : Pattern) (guard : d100941 p = 1) (decreasing : d0 p < d10648 p) :
    d48308 p + d10648 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 141 p
  rw [at141] at beforeRange
  have afterRange := bonus_range 119 (HazardPattern.afterPattern 10000 p (.walk 119))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) ∧ bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) ≤ 2 at afterRange
  rw [gammaAfter493] at afterRange
  have possibilities : (d10648 p = 1 ∧ d0 p = 0) ∨ (d10648 p = 2 ∧ d0 p = 0) ∨ (d10648 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro6896 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro23210 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare10083 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro23243 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare10084 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro23243 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10083 p complete
    omega
theorem local493 (p : Pattern) (guard : d100941 p = 1)
    (decreasing : bonus 119 (HazardPattern.afterPattern 10000 p (.walk 119)) < bonus 141 p) :
    NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 141 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 119) + NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 119))) + bonus 119 (HazardPattern.afterPattern 10000 p (.walk 119)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 119) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) < bonus 141 p at decreasing
  rw [gammaAfter493, at141] at decreasing
  have numeric := numeric493 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119))
  rw [oldBefore141, at141, literal, oldAfter493, gammaAfter493]
  exact numeric
theorem numeric494 (p : Pattern) (guard : d82381 p = 1) (decreasing : d0 p < d10648 p) :
    d48308 p + d10648 p ≤ (2 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 141 p
  rw [at141] at beforeRange
  have afterRange := bonus_range 119 (HazardPattern.afterPattern 10000 p (.push 119 (.stay 97)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 119 (.stay 97))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 97))) ∧ bonus (HazardPattern.nextHero (.push 119 (.stay 97))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 97))) ≤ 2 at afterRange
  rw [gammaAfter494] at afterRange
  have possibilities : (d10648 p = 1 ∧ d0 p = 0) ∨ (d10648 p = 2 ∧ d0 p = 0) ∨ (d10648 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro6896 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro23244 p guard beforeEq
    have complete := andIntro23245 p afterEq combined
    have bound := compare10631 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro23246 p guard beforeEq
    have complete := andIntro23247 p afterEq combined
    have bound := compare10975 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro23246 p guard beforeEq
    have complete := andIntro23248 p afterEq combined
    have bound := compare10085 p complete
    omega
theorem local494 (p : Pattern) (guard : d82381 p = 1)
    (decreasing : bonus 119 (HazardPattern.afterPattern 10000 p (.push 119 (.stay 97))) < bonus 141 p) :
    NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 141 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 119 (.stay 97)) + NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 119 (.stay 97)))) + bonus 119 (HazardPattern.afterPattern 10000 p (.push 119 (.stay 97))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 119 (.stay 97)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 119 (.stay 97))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 97))) < bonus 141 p at decreasing
  rw [gammaAfter494, at141] at decreasing
  have numeric := numeric494 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 119 (.stay 97))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 97)))
  rw [oldBefore141, at141, literal, oldAfter494, gammaAfter494]
  exact numeric
theorem numeric495 (p : Pattern) (guard : d129672 p = 1) (decreasing : d20389 p < d10648 p) :
    d48308 p + d10648 p ≤ (0 : Int) + d48997 p + d20389 p := by
  have beforeRange := bonus_range 141 p
  rw [at141] at beforeRange
  have afterRange := bonus_range 163 (HazardPattern.afterPattern 10000 p (.walk 163))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) ∧ bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) ≤ 2 at afterRange
  rw [gammaAfter495] at afterRange
  have possibilities : (d10648 p = 1 ∧ d20389 p = 0) ∨ (d10648 p = 2 ∧ d20389 p = 0) ∨ (d10648 p = 2 ∧ d20389 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro6896 p pair.1
    have afterEq := eqIntro10791 p pair.2
    have combined := andIntro23249 p beforeEq guard
    have complete := andIntro23390 p combined afterEq
    have bound := compare10976 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro10791 p pair.2
    have combined := andIntro23391 p beforeEq guard
    have complete := andIntro23425 p combined afterEq
    have bound := compare10977 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro10843 p pair.2
    have combined := andIntro23391 p beforeEq guard
    have complete := andIntro23453 p combined afterEq
    have bound := compare10976 p complete
    omega
theorem local495 (p : Pattern) (guard : d129672 p = 1)
    (decreasing : bonus 163 (HazardPattern.afterPattern 10000 p (.walk 163)) < bonus 141 p) :
    NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 141 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 163) + NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 163))) + bonus 163 (HazardPattern.afterPattern 10000 p (.walk 163)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 163) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) < bonus 141 p at decreasing
  rw [gammaAfter495, at141] at decreasing
  have numeric := numeric495 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163))
  rw [oldBefore141, at141, literal, oldAfter495, gammaAfter495]
  exact numeric
theorem numeric496 (p : Pattern) (guard : d130390 p = 1) (decreasing : d0 p < d10648 p) :
    d48308 p + d10648 p ≤ (4 : Int) + d130479 p + d0 p := by
  have beforeRange := bonus_range 141 p
  rw [at141] at beforeRange
  have afterRange := bonus_range 163 (HazardPattern.afterPattern 10000 p (.push 163 (.stay 185)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 163 (.stay 185))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 185))) ∧ bonus (HazardPattern.nextHero (.push 163 (.stay 185))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 185))) ≤ 2 at afterRange
  rw [gammaAfter496] at afterRange
  have possibilities : (d10648 p = 1 ∧ d0 p = 0) ∨ (d10648 p = 2 ∧ d0 p = 0) ∨ (d10648 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro6896 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro23565 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10978 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro23598 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10979 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro23598 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10978 p complete
    omega
theorem local496 (p : Pattern) (guard : d130390 p = 1)
    (decreasing : bonus 163 (HazardPattern.afterPattern 10000 p (.push 163 (.stay 185))) < bonus 141 p) :
    NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 141 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 163 (.stay 185)) + NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 163 (.stay 185)))) + bonus 163 (HazardPattern.afterPattern 10000 p (.push 163 (.stay 185))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 163 (.stay 185)) = (4 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 163 (.stay 185))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 185))) < bonus 141 p at decreasing
  rw [gammaAfter496, at141] at decreasing
  have numeric := numeric496 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 163 (.stay 185))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 185)))
  rw [oldBefore141, at141, literal, oldAfter496, gammaAfter496]
  exact numeric
theorem numeric497 (p : Pattern) (guard : d102105 p = 1) (decreasing : d0 p < d10648 p) :
    d48308 p + d10648 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 141 p
  rw [at141] at beforeRange
  have afterRange := bonus_range 120 (HazardPattern.afterPattern 10000 p (.walk 120))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) ∧ bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) ≤ 2 at afterRange
  rw [gammaAfter497] at afterRange
  have possibilities : (d10648 p = 1 ∧ d0 p = 0) ∨ (d10648 p = 2 ∧ d0 p = 0) ∨ (d10648 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro6896 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro23601 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare10083 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro23604 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare10084 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro23604 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10083 p complete
    omega
theorem local497 (p : Pattern) (guard : d102105 p = 1)
    (decreasing : bonus 120 (HazardPattern.afterPattern 10000 p (.walk 120)) < bonus 141 p) :
    NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 141 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 120) + NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 120))) + bonus 120 (HazardPattern.afterPattern 10000 p (.walk 120)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 120) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) < bonus 141 p at decreasing
  rw [gammaAfter497, at141] at decreasing
  have numeric := numeric497 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120))
  rw [oldBefore141, at141, literal, oldAfter497, gammaAfter497]
  exact numeric
theorem numeric498 (p : Pattern) (guard : d100942 p = 1) (decreasing : d0 p < d10648 p) :
    d48308 p + d10648 p ≤ (0 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 141 p
  rw [at141] at beforeRange
  have afterRange := bonus_range 118 (HazardPattern.afterPattern 10000 p (.walk 118))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) ∧ bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) ≤ 2 at afterRange
  rw [gammaAfter498] at afterRange
  have possibilities : (d10648 p = 1 ∧ d0 p = 0) ∨ (d10648 p = 2 ∧ d0 p = 0) ∨ (d10648 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro6896 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro23607 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare10083 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro23610 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare10084 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro23610 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare10083 p complete
    omega
theorem local498 (p : Pattern) (guard : d100942 p = 1)
    (decreasing : bonus 118 (HazardPattern.afterPattern 10000 p (.walk 118)) < bonus 141 p) :
    NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 141 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 118) + NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 118))) + bonus 118 (HazardPattern.afterPattern 10000 p (.walk 118)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 118) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) < bonus 141 p at decreasing
  rw [gammaAfter498, at141] at decreasing
  have numeric := numeric498 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118))
  rw [oldBefore141, at141, literal, oldAfter498, gammaAfter498]
  exact numeric
theorem numeric499 (p : Pattern) (guard : d130482 p = 1) (decreasing : d20891 p < d10648 p) :
    d48308 p + d10648 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 141 p
  rw [at141] at beforeRange
  have afterRange := bonus_range 164 (HazardPattern.afterPattern 10000 p (.walk 164))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) ∧ bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) ≤ 2 at afterRange
  rw [gammaAfter499] at afterRange
  have possibilities : (d10648 p = 1 ∧ d20891 p = 0) ∨ (d10648 p = 2 ∧ d20891 p = 0) ∨ (d10648 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro6896 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro23611 p beforeEq guard
    have complete := andIntro23692 p combined afterEq
    have bound := compare10980 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro23693 p beforeEq guard
    have complete := andIntro23727 p combined afterEq
    have bound := compare10981 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro23693 p beforeEq guard
    have complete := andIntro23755 p combined afterEq
    have bound := compare10980 p complete
    omega
theorem local499 (p : Pattern) (guard : d130482 p = 1)
    (decreasing : bonus 164 (HazardPattern.afterPattern 10000 p (.walk 164)) < bonus 141 p) :
    NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 141 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 164) + NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 164))) + bonus 164 (HazardPattern.afterPattern 10000 p (.walk 164)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 164) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) < bonus 141 p at decreasing
  rw [gammaAfter499, at141] at decreasing
  have numeric := numeric499 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164))
  rw [oldBefore141, at141, literal, oldAfter499, gammaAfter499]
  exact numeric
theorem numeric500 (p : Pattern) (guard : d131099 p = 1) (decreasing : d19737 p < d10648 p) :
    d48308 p + d10648 p ≤ (0 : Int) + d48749 p + d19737 p := by
  have beforeRange := bonus_range 141 p
  rw [at141] at beforeRange
  have afterRange := bonus_range 162 (HazardPattern.afterPattern 10000 p (.walk 162))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) ∧ bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) ≤ 2 at afterRange
  rw [gammaAfter500] at afterRange
  have possibilities : (d10648 p = 1 ∧ d19737 p = 0) ∨ (d10648 p = 2 ∧ d19737 p = 0) ∨ (d10648 p = 2 ∧ d19737 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro6896 p pair.1
    have afterEq := eqIntro11154 p pair.2
    have combined := andIntro23867 p beforeEq guard
    have complete := andIntro23972 p afterEq combined
    have bound := compare10982 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro11154 p pair.2
    have combined := andIntro24005 p beforeEq guard
    have complete := andIntro24039 p afterEq combined
    have bound := compare10983 p complete
    omega
  · have beforeEq := eqIntro10686 p pair.1
    have afterEq := eqIntro11224 p pair.2
    have combined := andIntro24005 p beforeEq guard
    have complete := andIntro24067 p combined afterEq
    have bound := compare10982 p complete
    omega
theorem local500 (p : Pattern) (guard : d131099 p = 1)
    (decreasing : bonus 162 (HazardPattern.afterPattern 10000 p (.walk 162)) < bonus 141 p) :
    NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 141 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 162) + NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 162))) + bonus 162 (HazardPattern.afterPattern 10000 p (.walk 162)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 162) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) < bonus 141 p at decreasing
  rw [gammaAfter500, at141] at decreasing
  have numeric := numeric500 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162))
  rw [oldBefore141, at141, literal, oldAfter500, gammaAfter500]
  exact numeric
theorem numeric501 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 144 p
  rw [at144] at beforeRange
  have afterRange := bonus_range 122 (HazardPattern.afterPattern 10000 p (.walk 122))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) ∧ bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) ≤ 2 at afterRange
  rw [gammaAfter501] at afterRange
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
theorem local501 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 122 (HazardPattern.afterPattern 10000 p (.walk 122)) < bonus 144 p) :
    NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 144 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 122) + NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 122))) + bonus 122 (HazardPattern.afterPattern 10000 p (.walk 122)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 122) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) < bonus 144 p at decreasing
  rw [gammaAfter501, at144] at decreasing
  have numeric := numeric501 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122))
  rw [oldBefore144, at144, literal, oldAfter501, gammaAfter501]
  exact numeric
theorem numeric502 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 144 p
  rw [at144] at beforeRange
  have afterRange := bonus_range 122 (HazardPattern.afterPattern 10000 p (.push 122 (.stay 100)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 122 (.stay 100))) (HazardPattern.afterPattern 10000 p (.push 122 (.stay 100))) ∧ bonus (HazardPattern.nextHero (.push 122 (.stay 100))) (HazardPattern.afterPattern 10000 p (.push 122 (.stay 100))) ≤ 2 at afterRange
  rw [gammaAfter502] at afterRange
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
theorem local502 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 122 (HazardPattern.afterPattern 10000 p (.push 122 (.stay 100))) < bonus 144 p) :
    NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 144 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 122 (.stay 100)) + NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 122 (.stay 100)))) + bonus 122 (HazardPattern.afterPattern 10000 p (.push 122 (.stay 100))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 122 (.stay 100)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 122 (.stay 100))) (HazardPattern.afterPattern 10000 p (.push 122 (.stay 100))) < bonus 144 p at decreasing
  rw [gammaAfter502, at144] at decreasing
  have numeric := numeric502 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 122 (.stay 100))) (HazardPattern.afterPattern 10000 p (.push 122 (.stay 100)))
  rw [oldBefore144, at144, literal, oldAfter502, gammaAfter502]
  exact numeric
theorem numeric503 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 144 p
  rw [at144] at beforeRange
  have afterRange := bonus_range 166 (HazardPattern.afterPattern 10000 p (.walk 166))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) ∧ bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) ≤ 2 at afterRange
  rw [gammaAfter503] at afterRange
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
theorem local503 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 166 (HazardPattern.afterPattern 10000 p (.walk 166)) < bonus 144 p) :
    NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 144 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 166) + NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 166))) + bonus 166 (HazardPattern.afterPattern 10000 p (.walk 166)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 166) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) < bonus 144 p at decreasing
  rw [gammaAfter503, at144] at decreasing
  have numeric := numeric503 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166))
  rw [oldBefore144, at144, literal, oldAfter503, gammaAfter503]
  exact numeric
theorem numeric504 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 144 p
  rw [at144] at beforeRange
  have afterRange := bonus_range 166 (HazardPattern.afterPattern 10000 p (.push 166 (.stay 188)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 166 (.stay 188))) (HazardPattern.afterPattern 10000 p (.push 166 (.stay 188))) ∧ bonus (HazardPattern.nextHero (.push 166 (.stay 188))) (HazardPattern.afterPattern 10000 p (.push 166 (.stay 188))) ≤ 2 at afterRange
  rw [gammaAfter504] at afterRange
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
theorem local504 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 166 (HazardPattern.afterPattern 10000 p (.push 166 (.stay 188))) < bonus 144 p) :
    NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 144 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 166 (.stay 188)) + NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 166 (.stay 188)))) + bonus 166 (HazardPattern.afterPattern 10000 p (.push 166 (.stay 188))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 166 (.stay 188)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 166 (.stay 188))) (HazardPattern.afterPattern 10000 p (.push 166 (.stay 188))) < bonus 144 p at decreasing
  rw [gammaAfter504, at144] at decreasing
  have numeric := numeric504 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 166 (.stay 188))) (HazardPattern.afterPattern 10000 p (.push 166 (.stay 188)))
  rw [oldBefore144, at144, literal, oldAfter504, gammaAfter504]
  exact numeric
theorem numeric505 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 144 p
  rw [at144] at beforeRange
  have afterRange := bonus_range 145 (HazardPattern.afterPattern 10000 p (.walk 145))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ∧ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ≤ 2 at afterRange
  rw [gammaAfter505] at afterRange
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
theorem local505 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 144 p) :
    NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 144 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 145) + NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) + bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 145) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 144 p at decreasing
  rw [gammaAfter505, at144] at decreasing
  have numeric := numeric505 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145))
  rw [oldBefore144, at144, literal, oldAfter505, gammaAfter505]
  exact numeric
theorem numeric506 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 144 p
  rw [at144] at beforeRange
  have afterRange := bonus_range 145 (HazardPattern.afterPattern 10000 p (.push 145 (.stay 146)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 145 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 146))) ∧ bonus (HazardPattern.nextHero (.push 145 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 146))) ≤ 2 at afterRange
  rw [gammaAfter506] at afterRange
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
theorem local506 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 145 (HazardPattern.afterPattern 10000 p (.push 145 (.stay 146))) < bonus 144 p) :
    NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 144 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 145 (.stay 146)) + NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 145 (.stay 146)))) + bonus 145 (HazardPattern.afterPattern 10000 p (.push 145 (.stay 146))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 145 (.stay 146)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 145 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 146))) < bonus 144 p at decreasing
  rw [gammaAfter506, at144] at decreasing
  have numeric := numeric506 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 145 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 146)))
  rw [oldBefore144, at144, literal, oldAfter506, gammaAfter506]
  exact numeric
theorem numeric507 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 144 p
  rw [at144] at beforeRange
  have afterRange := bonus_range 123 (HazardPattern.afterPattern 10000 p (.walk 123))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ∧ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ≤ 2 at afterRange
  rw [gammaAfter507] at afterRange
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
theorem local507 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 144 p) :
    NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 144 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 123) + NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) + bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 123) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 144 p at decreasing
  rw [gammaAfter507, at144] at decreasing
  have numeric := numeric507 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123))
  rw [oldBefore144, at144, literal, oldAfter507, gammaAfter507]
  exact numeric
theorem numeric508 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 144 p
  rw [at144] at beforeRange
  have afterRange := bonus_range 167 (HazardPattern.afterPattern 10000 p (.walk 167))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ∧ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ≤ 2 at afterRange
  rw [gammaAfter508] at afterRange
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
theorem local508 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 144 p) :
    NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 144 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 167) + NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) + bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 167) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 144 p at decreasing
  rw [gammaAfter508, at144] at decreasing
  have numeric := numeric508 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167))
  rw [oldBefore144, at144, literal, oldAfter508, gammaAfter508]
  exact numeric
theorem numeric509 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 145 p
  rw [at145] at beforeRange
  have afterRange := bonus_range 123 (HazardPattern.afterPattern 10000 p (.walk 123))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ∧ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ≤ 2 at afterRange
  rw [gammaAfter509] at afterRange
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
theorem local509 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 145 p) :
    NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 145 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 123) + NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) + bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 123) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 145 p at decreasing
  rw [gammaAfter509, at145] at decreasing
  have numeric := numeric509 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123))
  rw [oldBefore145, at145, literal, oldAfter509, gammaAfter509]
  exact numeric
theorem numeric510 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 145 p
  rw [at145] at beforeRange
  have afterRange := bonus_range 123 (HazardPattern.afterPattern 10000 p (.push 123 (.stay 101)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 123 (.stay 101))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 101))) ∧ bonus (HazardPattern.nextHero (.push 123 (.stay 101))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 101))) ≤ 2 at afterRange
  rw [gammaAfter510] at afterRange
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
theorem local510 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 123 (HazardPattern.afterPattern 10000 p (.push 123 (.stay 101))) < bonus 145 p) :
    NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 145 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 123 (.stay 101)) + NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 123 (.stay 101)))) + bonus 123 (HazardPattern.afterPattern 10000 p (.push 123 (.stay 101))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 123 (.stay 101)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 123 (.stay 101))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 101))) < bonus 145 p at decreasing
  rw [gammaAfter510, at145] at decreasing
  have numeric := numeric510 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 123 (.stay 101))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 101)))
  rw [oldBefore145, at145, literal, oldAfter510, gammaAfter510]
  exact numeric
theorem numeric511 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 145 p
  rw [at145] at beforeRange
  have afterRange := bonus_range 167 (HazardPattern.afterPattern 10000 p (.walk 167))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ∧ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ≤ 2 at afterRange
  rw [gammaAfter511] at afterRange
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
theorem local511 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 145 p) :
    NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 145 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 167) + NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) + bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 167) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 145 p at decreasing
  rw [gammaAfter511, at145] at decreasing
  have numeric := numeric511 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167))
  rw [oldBefore145, at145, literal, oldAfter511, gammaAfter511]
  exact numeric
theorem numeric512 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 145 p
  rw [at145] at beforeRange
  have afterRange := bonus_range 167 (HazardPattern.afterPattern 10000 p (.push 167 (.stay 189)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 167 (.stay 189))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 189))) ∧ bonus (HazardPattern.nextHero (.push 167 (.stay 189))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 189))) ≤ 2 at afterRange
  rw [gammaAfter512] at afterRange
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
theorem local512 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 167 (HazardPattern.afterPattern 10000 p (.push 167 (.stay 189))) < bonus 145 p) :
    NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 145 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 167 (.stay 189)) + NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 167 (.stay 189)))) + bonus 167 (HazardPattern.afterPattern 10000 p (.push 167 (.stay 189))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 167 (.stay 189)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 167 (.stay 189))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 189))) < bonus 145 p at decreasing
  rw [gammaAfter512, at145] at decreasing
  have numeric := numeric512 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 167 (.stay 189))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 189)))
  rw [oldBefore145, at145, literal, oldAfter512, gammaAfter512]
  exact numeric
theorem numeric513 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 145 p
  rw [at145] at beforeRange
  have afterRange := bonus_range 146 (HazardPattern.afterPattern 10000 p (.walk 146))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ∧ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ≤ 2 at afterRange
  rw [gammaAfter513] at afterRange
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
theorem local513 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 145 p) :
    NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 145 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 146) + NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) + bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 146) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 145 p at decreasing
  rw [gammaAfter513, at145] at decreasing
  have numeric := numeric513 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146))
  rw [oldBefore145, at145, literal, oldAfter513, gammaAfter513]
  exact numeric
theorem numeric514 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 145 p
  rw [at145] at beforeRange
  have afterRange := bonus_range 146 (HazardPattern.afterPattern 10000 p (.push 146 (.stay 147)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 146 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 147))) ∧ bonus (HazardPattern.nextHero (.push 146 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 147))) ≤ 2 at afterRange
  rw [gammaAfter514] at afterRange
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
theorem local514 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 146 (HazardPattern.afterPattern 10000 p (.push 146 (.stay 147))) < bonus 145 p) :
    NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 145 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 146 (.stay 147)) + NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 146 (.stay 147)))) + bonus 146 (HazardPattern.afterPattern 10000 p (.push 146 (.stay 147))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 146 (.stay 147)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 146 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 147))) < bonus 145 p at decreasing
  rw [gammaAfter514, at145] at decreasing
  have numeric := numeric514 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 146 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 147)))
  rw [oldBefore145, at145, literal, oldAfter514, gammaAfter514]
  exact numeric
theorem numeric515 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 145 p
  rw [at145] at beforeRange
  have afterRange := bonus_range 144 (HazardPattern.afterPattern 10000 p (.walk 144))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) ∧ bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) ≤ 2 at afterRange
  rw [gammaAfter515] at afterRange
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
theorem local515 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 144 (HazardPattern.afterPattern 10000 p (.walk 144)) < bonus 145 p) :
    NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 145 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 144) + NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 144))) + bonus 144 (HazardPattern.afterPattern 10000 p (.walk 144)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 144) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) < bonus 145 p at decreasing
  rw [gammaAfter515, at145] at decreasing
  have numeric := numeric515 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144))
  rw [oldBefore145, at145, literal, oldAfter515, gammaAfter515]
  exact numeric
theorem numeric516 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 145 p
  rw [at145] at beforeRange
  have afterRange := bonus_range 124 (HazardPattern.afterPattern 10000 p (.walk 124))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ∧ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ≤ 2 at afterRange
  rw [gammaAfter516] at afterRange
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
theorem local516 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 145 p) :
    NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 145 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 124) + NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) + bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 124) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 145 p at decreasing
  rw [gammaAfter516, at145] at decreasing
  have numeric := numeric516 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124))
  rw [oldBefore145, at145, literal, oldAfter516, gammaAfter516]
  exact numeric
theorem numeric517 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 145 p
  rw [at145] at beforeRange
  have afterRange := bonus_range 122 (HazardPattern.afterPattern 10000 p (.walk 122))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) ∧ bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) ≤ 2 at afterRange
  rw [gammaAfter517] at afterRange
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
theorem local517 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 122 (HazardPattern.afterPattern 10000 p (.walk 122)) < bonus 145 p) :
    NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 145 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 122) + NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 122))) + bonus 122 (HazardPattern.afterPattern 10000 p (.walk 122)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 122) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) < bonus 145 p at decreasing
  rw [gammaAfter517, at145] at decreasing
  have numeric := numeric517 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122))
  rw [oldBefore145, at145, literal, oldAfter517, gammaAfter517]
  exact numeric
theorem numeric518 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 145 p
  rw [at145] at beforeRange
  have afterRange := bonus_range 168 (HazardPattern.afterPattern 10000 p (.walk 168))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ∧ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ≤ 2 at afterRange
  rw [gammaAfter518] at afterRange
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
theorem local518 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 145 p) :
    NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 145 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 168) + NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) + bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 168) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 145 p at decreasing
  rw [gammaAfter518, at145] at decreasing
  have numeric := numeric518 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168))
  rw [oldBefore145, at145, literal, oldAfter518, gammaAfter518]
  exact numeric
theorem numeric519 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 145 p
  rw [at145] at beforeRange
  have afterRange := bonus_range 166 (HazardPattern.afterPattern 10000 p (.walk 166))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) ∧ bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) ≤ 2 at afterRange
  rw [gammaAfter519] at afterRange
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
theorem local519 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 166 (HazardPattern.afterPattern 10000 p (.walk 166)) < bonus 145 p) :
    NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 145 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 166) + NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 166))) + bonus 166 (HazardPattern.afterPattern 10000 p (.walk 166)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 166) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) < bonus 145 p at decreasing
  rw [gammaAfter519, at145] at decreasing
  have numeric := numeric519 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166))
  rw [oldBefore145, at145, literal, oldAfter519, gammaAfter519]
  exact numeric
theorem numeric520 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 146 p
  rw [at146] at beforeRange
  have afterRange := bonus_range 124 (HazardPattern.afterPattern 10000 p (.walk 124))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ∧ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ≤ 2 at afterRange
  rw [gammaAfter520] at afterRange
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
theorem local520 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 124) + NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) + bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 124) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 146 p at decreasing
  rw [gammaAfter520, at146] at decreasing
  have numeric := numeric520 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124))
  rw [oldBefore146, at146, literal, oldAfter520, gammaAfter520]
  exact numeric
theorem numeric521 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 146 p
  rw [at146] at beforeRange
  have afterRange := bonus_range 124 (HazardPattern.afterPattern 10000 p (.push 124 (.stay 102)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 124 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 102))) ∧ bonus (HazardPattern.nextHero (.push 124 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 102))) ≤ 2 at afterRange
  rw [gammaAfter521] at afterRange
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
theorem local521 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 124 (HazardPattern.afterPattern 10000 p (.push 124 (.stay 102))) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 124 (.stay 102)) + NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 124 (.stay 102)))) + bonus 124 (HazardPattern.afterPattern 10000 p (.push 124 (.stay 102))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 124 (.stay 102)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 124 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 102))) < bonus 146 p at decreasing
  rw [gammaAfter521, at146] at decreasing
  have numeric := numeric521 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 124 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 102)))
  rw [oldBefore146, at146, literal, oldAfter521, gammaAfter521]
  exact numeric
theorem numeric522 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 146 p
  rw [at146] at beforeRange
  have afterRange := bonus_range 168 (HazardPattern.afterPattern 10000 p (.walk 168))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ∧ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ≤ 2 at afterRange
  rw [gammaAfter522] at afterRange
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
theorem local522 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 168) + NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) + bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 168) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 146 p at decreasing
  rw [gammaAfter522, at146] at decreasing
  have numeric := numeric522 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168))
  rw [oldBefore146, at146, literal, oldAfter522, gammaAfter522]
  exact numeric
theorem numeric523 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 146 p
  rw [at146] at beforeRange
  have afterRange := bonus_range 168 (HazardPattern.afterPattern 10000 p (.push 168 (.stay 190)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 168 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 190))) ∧ bonus (HazardPattern.nextHero (.push 168 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 190))) ≤ 2 at afterRange
  rw [gammaAfter523] at afterRange
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
theorem local523 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 168 (HazardPattern.afterPattern 10000 p (.push 168 (.stay 190))) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 168 (.stay 190)) + NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 168 (.stay 190)))) + bonus 168 (HazardPattern.afterPattern 10000 p (.push 168 (.stay 190))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 168 (.stay 190)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 168 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 190))) < bonus 146 p at decreasing
  rw [gammaAfter523, at146] at decreasing
  have numeric := numeric523 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 168 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 190)))
  rw [oldBefore146, at146, literal, oldAfter523, gammaAfter523]
  exact numeric
theorem numeric524 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 146 p
  rw [at146] at beforeRange
  have afterRange := bonus_range 147 (HazardPattern.afterPattern 10000 p (.walk 147))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ∧ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ≤ 2 at afterRange
  rw [gammaAfter524] at afterRange
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
theorem local524 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 147) + NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) + bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 147) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 146 p at decreasing
  rw [gammaAfter524, at146] at decreasing
  have numeric := numeric524 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147))
  rw [oldBefore146, at146, literal, oldAfter524, gammaAfter524]
  exact numeric
theorem numeric525 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 146 p
  rw [at146] at beforeRange
  have afterRange := bonus_range 147 (HazardPattern.afterPattern 10000 p (.push 147 (.stay 148)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 147 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 148))) ∧ bonus (HazardPattern.nextHero (.push 147 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 148))) ≤ 2 at afterRange
  rw [gammaAfter525] at afterRange
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
theorem local525 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 147 (HazardPattern.afterPattern 10000 p (.push 147 (.stay 148))) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 147 (.stay 148)) + NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 147 (.stay 148)))) + bonus 147 (HazardPattern.afterPattern 10000 p (.push 147 (.stay 148))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 147 (.stay 148)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 147 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 148))) < bonus 146 p at decreasing
  rw [gammaAfter525, at146] at decreasing
  have numeric := numeric525 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 147 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 148)))
  rw [oldBefore146, at146, literal, oldAfter525, gammaAfter525]
  exact numeric
theorem numeric526 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 146 p
  rw [at146] at beforeRange
  have afterRange := bonus_range 145 (HazardPattern.afterPattern 10000 p (.walk 145))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ∧ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ≤ 2 at afterRange
  rw [gammaAfter526] at afterRange
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
theorem local526 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 145) + NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) + bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 145) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 146 p at decreasing
  rw [gammaAfter526, at146] at decreasing
  have numeric := numeric526 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145))
  rw [oldBefore146, at146, literal, oldAfter526, gammaAfter526]
  exact numeric
theorem numeric527 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 146 p
  rw [at146] at beforeRange
  have afterRange := bonus_range 145 (HazardPattern.afterPattern 10000 p (.push 145 (.stay 144)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 145 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 144))) ∧ bonus (HazardPattern.nextHero (.push 145 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 144))) ≤ 2 at afterRange
  rw [gammaAfter527] at afterRange
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
theorem local527 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 145 (HazardPattern.afterPattern 10000 p (.push 145 (.stay 144))) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 145 (.stay 144)) + NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 145 (.stay 144)))) + bonus 145 (HazardPattern.afterPattern 10000 p (.push 145 (.stay 144))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 145 (.stay 144)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 145 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 144))) < bonus 146 p at decreasing
  rw [gammaAfter527, at146] at decreasing
  have numeric := numeric527 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 145 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 144)))
  rw [oldBefore146, at146, literal, oldAfter527, gammaAfter527]
  exact numeric
theorem numeric528 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 146 p
  rw [at146] at beforeRange
  have afterRange := bonus_range 125 (HazardPattern.afterPattern 10000 p (.walk 125))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ∧ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ≤ 2 at afterRange
  rw [gammaAfter528] at afterRange
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
theorem local528 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 125) + NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) + bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 125) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 146 p at decreasing
  rw [gammaAfter528, at146] at decreasing
  have numeric := numeric528 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125))
  rw [oldBefore146, at146, literal, oldAfter528, gammaAfter528]
  exact numeric
theorem numeric529 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 146 p
  rw [at146] at beforeRange
  have afterRange := bonus_range 123 (HazardPattern.afterPattern 10000 p (.walk 123))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ∧ bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) ≤ 2 at afterRange
  rw [gammaAfter529] at afterRange
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
theorem local529 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 123) + NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) + bonus 123 (HazardPattern.afterPattern 10000 p (.walk 123)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 123) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) < bonus 146 p at decreasing
  rw [gammaAfter529, at146] at decreasing
  have numeric := numeric529 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123))
  rw [oldBefore146, at146, literal, oldAfter529, gammaAfter529]
  exact numeric
theorem numeric530 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 146 p
  rw [at146] at beforeRange
  have afterRange := bonus_range 169 (HazardPattern.afterPattern 10000 p (.walk 169))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ∧ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ≤ 2 at afterRange
  rw [gammaAfter530] at afterRange
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
theorem local530 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 169) + NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) + bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 169) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 146 p at decreasing
  rw [gammaAfter530, at146] at decreasing
  have numeric := numeric530 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169))
  rw [oldBefore146, at146, literal, oldAfter530, gammaAfter530]
  exact numeric
theorem numeric531 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 146 p
  rw [at146] at beforeRange
  have afterRange := bonus_range 167 (HazardPattern.afterPattern 10000 p (.walk 167))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ∧ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ≤ 2 at afterRange
  rw [gammaAfter531] at afterRange
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
theorem local531 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 167) + NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) + bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 167) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 146 p at decreasing
  rw [gammaAfter531, at146] at decreasing
  have numeric := numeric531 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167))
  rw [oldBefore146, at146, literal, oldAfter531, gammaAfter531]
  exact numeric
theorem numeric532 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 147 p
  rw [at147] at beforeRange
  have afterRange := bonus_range 125 (HazardPattern.afterPattern 10000 p (.walk 125))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ∧ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ≤ 2 at afterRange
  rw [gammaAfter532] at afterRange
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
theorem local532 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 125) + NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) + bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 125) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 147 p at decreasing
  rw [gammaAfter532, at147] at decreasing
  have numeric := numeric532 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125))
  rw [oldBefore147, at147, literal, oldAfter532, gammaAfter532]
  exact numeric
theorem numeric533 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 147 p
  rw [at147] at beforeRange
  have afterRange := bonus_range 125 (HazardPattern.afterPattern 10000 p (.push 125 (.stay 103)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 125 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 103))) ∧ bonus (HazardPattern.nextHero (.push 125 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 103))) ≤ 2 at afterRange
  rw [gammaAfter533] at afterRange
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
theorem local533 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 125 (HazardPattern.afterPattern 10000 p (.push 125 (.stay 103))) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 125 (.stay 103)) + NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 125 (.stay 103)))) + bonus 125 (HazardPattern.afterPattern 10000 p (.push 125 (.stay 103))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 125 (.stay 103)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 125 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 103))) < bonus 147 p at decreasing
  rw [gammaAfter533, at147] at decreasing
  have numeric := numeric533 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 125 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 103)))
  rw [oldBefore147, at147, literal, oldAfter533, gammaAfter533]
  exact numeric
theorem numeric534 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 147 p
  rw [at147] at beforeRange
  have afterRange := bonus_range 169 (HazardPattern.afterPattern 10000 p (.walk 169))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ∧ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ≤ 2 at afterRange
  rw [gammaAfter534] at afterRange
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
theorem local534 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 169) + NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) + bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 169) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 147 p at decreasing
  rw [gammaAfter534, at147] at decreasing
  have numeric := numeric534 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169))
  rw [oldBefore147, at147, literal, oldAfter534, gammaAfter534]
  exact numeric
theorem numeric535 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 147 p
  rw [at147] at beforeRange
  have afterRange := bonus_range 169 (HazardPattern.afterPattern 10000 p (.push 169 (.stay 191)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 169 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 191))) ∧ bonus (HazardPattern.nextHero (.push 169 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 191))) ≤ 2 at afterRange
  rw [gammaAfter535] at afterRange
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
theorem local535 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 169 (HazardPattern.afterPattern 10000 p (.push 169 (.stay 191))) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 169 (.stay 191)) + NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 169 (.stay 191)))) + bonus 169 (HazardPattern.afterPattern 10000 p (.push 169 (.stay 191))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 169 (.stay 191)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 169 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 191))) < bonus 147 p at decreasing
  rw [gammaAfter535, at147] at decreasing
  have numeric := numeric535 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 169 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 191)))
  rw [oldBefore147, at147, literal, oldAfter535, gammaAfter535]
  exact numeric
theorem numeric536 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 147 p
  rw [at147] at beforeRange
  have afterRange := bonus_range 148 (HazardPattern.afterPattern 10000 p (.walk 148))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ∧ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ≤ 2 at afterRange
  rw [gammaAfter536] at afterRange
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
theorem local536 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 148) + NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 148))) + bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 148) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 147 p at decreasing
  rw [gammaAfter536, at147] at decreasing
  have numeric := numeric536 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148))
  rw [oldBefore147, at147, literal, oldAfter536, gammaAfter536]
  exact numeric
theorem numeric537 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 147 p
  rw [at147] at beforeRange
  have afterRange := bonus_range 148 (HazardPattern.afterPattern 10000 p (.push 148 (.stay 149)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 148 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 149))) ∧ bonus (HazardPattern.nextHero (.push 148 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 149))) ≤ 2 at afterRange
  rw [gammaAfter537] at afterRange
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
theorem local537 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 148 (HazardPattern.afterPattern 10000 p (.push 148 (.stay 149))) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 148 (.stay 149)) + NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 148 (.stay 149)))) + bonus 148 (HazardPattern.afterPattern 10000 p (.push 148 (.stay 149))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 148 (.stay 149)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 148 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 149))) < bonus 147 p at decreasing
  rw [gammaAfter537, at147] at decreasing
  have numeric := numeric537 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 148 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 149)))
  rw [oldBefore147, at147, literal, oldAfter537, gammaAfter537]
  exact numeric
theorem numeric538 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 147 p
  rw [at147] at beforeRange
  have afterRange := bonus_range 146 (HazardPattern.afterPattern 10000 p (.walk 146))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ∧ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ≤ 2 at afterRange
  rw [gammaAfter538] at afterRange
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
theorem local538 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 146) + NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) + bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 146) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 147 p at decreasing
  rw [gammaAfter538, at147] at decreasing
  have numeric := numeric538 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146))
  rw [oldBefore147, at147, literal, oldAfter538, gammaAfter538]
  exact numeric
theorem numeric539 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 147 p
  rw [at147] at beforeRange
  have afterRange := bonus_range 146 (HazardPattern.afterPattern 10000 p (.push 146 (.stay 145)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 146 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 145))) ∧ bonus (HazardPattern.nextHero (.push 146 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 145))) ≤ 2 at afterRange
  rw [gammaAfter539] at afterRange
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
theorem local539 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 146 (HazardPattern.afterPattern 10000 p (.push 146 (.stay 145))) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 146 (.stay 145)) + NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 146 (.stay 145)))) + bonus 146 (HazardPattern.afterPattern 10000 p (.push 146 (.stay 145))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 146 (.stay 145)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 146 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 145))) < bonus 147 p at decreasing
  rw [gammaAfter539, at147] at decreasing
  have numeric := numeric539 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 146 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 145)))
  rw [oldBefore147, at147, literal, oldAfter539, gammaAfter539]
  exact numeric
theorem numeric540 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 147 p
  rw [at147] at beforeRange
  have afterRange := bonus_range 126 (HazardPattern.afterPattern 10000 p (.walk 126))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ∧ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ≤ 2 at afterRange
  rw [gammaAfter540] at afterRange
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
theorem local540 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 126) + NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 126))) + bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 126) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 147 p at decreasing
  rw [gammaAfter540, at147] at decreasing
  have numeric := numeric540 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126))
  rw [oldBefore147, at147, literal, oldAfter540, gammaAfter540]
  exact numeric
theorem numeric541 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 147 p
  rw [at147] at beforeRange
  have afterRange := bonus_range 124 (HazardPattern.afterPattern 10000 p (.walk 124))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ∧ bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) ≤ 2 at afterRange
  rw [gammaAfter541] at afterRange
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
theorem local541 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 124) + NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) + bonus 124 (HazardPattern.afterPattern 10000 p (.walk 124)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 124) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) < bonus 147 p at decreasing
  rw [gammaAfter541, at147] at decreasing
  have numeric := numeric541 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124))
  rw [oldBefore147, at147, literal, oldAfter541, gammaAfter541]
  exact numeric
theorem numeric542 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 147 p
  rw [at147] at beforeRange
  have afterRange := bonus_range 170 (HazardPattern.afterPattern 10000 p (.walk 170))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ∧ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ≤ 2 at afterRange
  rw [gammaAfter542] at afterRange
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
theorem local542 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 170) + NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 170))) + bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 170) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 147 p at decreasing
  rw [gammaAfter542, at147] at decreasing
  have numeric := numeric542 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170))
  rw [oldBefore147, at147, literal, oldAfter542, gammaAfter542]
  exact numeric
theorem numeric543 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 147 p
  rw [at147] at beforeRange
  have afterRange := bonus_range 168 (HazardPattern.afterPattern 10000 p (.walk 168))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ∧ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ≤ 2 at afterRange
  rw [gammaAfter543] at afterRange
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
theorem local543 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 168) + NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) + bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 168) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 147 p at decreasing
  rw [gammaAfter543, at147] at decreasing
  have numeric := numeric543 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168))
  rw [oldBefore147, at147, literal, oldAfter543, gammaAfter543]
  exact numeric
theorem numeric544 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 148 p
  rw [at148] at beforeRange
  have afterRange := bonus_range 126 (HazardPattern.afterPattern 10000 p (.walk 126))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ∧ bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) ≤ 2 at afterRange
  rw [gammaAfter544] at afterRange
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
theorem local544 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 126) + NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 126))) + bonus 126 (HazardPattern.afterPattern 10000 p (.walk 126)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 126) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) < bonus 148 p at decreasing
  rw [gammaAfter544, at148] at decreasing
  have numeric := numeric544 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126))
  rw [oldBefore148, at148, literal, oldAfter544, gammaAfter544]
  exact numeric
theorem numeric545 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 148 p
  rw [at148] at beforeRange
  have afterRange := bonus_range 126 (HazardPattern.afterPattern 10000 p (.push 126 (.stay 104)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 126 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 104))) ∧ bonus (HazardPattern.nextHero (.push 126 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 104))) ≤ 2 at afterRange
  rw [gammaAfter545] at afterRange
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
theorem local545 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 126 (HazardPattern.afterPattern 10000 p (.push 126 (.stay 104))) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 126 (.stay 104)) + NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 126 (.stay 104)))) + bonus 126 (HazardPattern.afterPattern 10000 p (.push 126 (.stay 104))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 126 (.stay 104)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 126 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 104))) < bonus 148 p at decreasing
  rw [gammaAfter545, at148] at decreasing
  have numeric := numeric545 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 126 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 104)))
  rw [oldBefore148, at148, literal, oldAfter545, gammaAfter545]
  exact numeric
theorem numeric546 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 148 p
  rw [at148] at beforeRange
  have afterRange := bonus_range 170 (HazardPattern.afterPattern 10000 p (.walk 170))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ∧ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ≤ 2 at afterRange
  rw [gammaAfter546] at afterRange
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
theorem local546 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 170) + NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 170))) + bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 170) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 148 p at decreasing
  rw [gammaAfter546, at148] at decreasing
  have numeric := numeric546 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170))
  rw [oldBefore148, at148, literal, oldAfter546, gammaAfter546]
  exact numeric
theorem numeric547 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 148 p
  rw [at148] at beforeRange
  have afterRange := bonus_range 170 (HazardPattern.afterPattern 10000 p (.push 170 (.stay 192)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 170 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 192))) ∧ bonus (HazardPattern.nextHero (.push 170 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 192))) ≤ 2 at afterRange
  rw [gammaAfter547] at afterRange
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
theorem local547 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 170 (HazardPattern.afterPattern 10000 p (.push 170 (.stay 192))) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 170 (.stay 192)) + NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 170 (.stay 192)))) + bonus 170 (HazardPattern.afterPattern 10000 p (.push 170 (.stay 192))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 170 (.stay 192)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 170 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 192))) < bonus 148 p at decreasing
  rw [gammaAfter547, at148] at decreasing
  have numeric := numeric547 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 170 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 192)))
  rw [oldBefore148, at148, literal, oldAfter547, gammaAfter547]
  exact numeric
theorem numeric548 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 148 p
  rw [at148] at beforeRange
  have afterRange := bonus_range 149 (HazardPattern.afterPattern 10000 p (.walk 149))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ∧ bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) ≤ 2 at afterRange
  rw [gammaAfter548] at afterRange
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
theorem local548 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 149) + NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) + bonus 149 (HazardPattern.afterPattern 10000 p (.walk 149)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 149) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) < bonus 148 p at decreasing
  rw [gammaAfter548, at148] at decreasing
  have numeric := numeric548 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149))
  rw [oldBefore148, at148, literal, oldAfter548, gammaAfter548]
  exact numeric
theorem numeric549 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 148 p
  rw [at148] at beforeRange
  have afterRange := bonus_range 149 (HazardPattern.afterPattern 10000 p (.push 149 (.stay 150)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 149 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 150))) ∧ bonus (HazardPattern.nextHero (.push 149 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 150))) ≤ 2 at afterRange
  rw [gammaAfter549] at afterRange
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
theorem local549 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 149 (HazardPattern.afterPattern 10000 p (.push 149 (.stay 150))) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 149 (.stay 150)) + NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 149 (.stay 150)))) + bonus 149 (HazardPattern.afterPattern 10000 p (.push 149 (.stay 150))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 149 (.stay 150)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 149 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 150))) < bonus 148 p at decreasing
  rw [gammaAfter549, at148] at decreasing
  have numeric := numeric549 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 149 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 150)))
  rw [oldBefore148, at148, literal, oldAfter549, gammaAfter549]
  exact numeric
theorem numeric550 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 148 p
  rw [at148] at beforeRange
  have afterRange := bonus_range 147 (HazardPattern.afterPattern 10000 p (.walk 147))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ∧ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ≤ 2 at afterRange
  rw [gammaAfter550] at afterRange
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
theorem local550 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 147) + NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) + bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 147) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 148 p at decreasing
  rw [gammaAfter550, at148] at decreasing
  have numeric := numeric550 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147))
  rw [oldBefore148, at148, literal, oldAfter550, gammaAfter550]
  exact numeric
theorem numeric551 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 148 p
  rw [at148] at beforeRange
  have afterRange := bonus_range 147 (HazardPattern.afterPattern 10000 p (.push 147 (.stay 146)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 147 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 146))) ∧ bonus (HazardPattern.nextHero (.push 147 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 146))) ≤ 2 at afterRange
  rw [gammaAfter551] at afterRange
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
theorem local551 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 147 (HazardPattern.afterPattern 10000 p (.push 147 (.stay 146))) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 147 (.stay 146)) + NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 147 (.stay 146)))) + bonus 147 (HazardPattern.afterPattern 10000 p (.push 147 (.stay 146))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 147 (.stay 146)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 147 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 146))) < bonus 148 p at decreasing
  rw [gammaAfter551, at148] at decreasing
  have numeric := numeric551 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 147 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 146)))
  rw [oldBefore148, at148, literal, oldAfter551, gammaAfter551]
  exact numeric
theorem numeric552 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 148 p
  rw [at148] at beforeRange
  have afterRange := bonus_range 127 (HazardPattern.afterPattern 10000 p (.walk 127))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ∧ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ≤ 2 at afterRange
  rw [gammaAfter552] at afterRange
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
theorem local552 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 127) + NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) + bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 127) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 148 p at decreasing
  rw [gammaAfter552, at148] at decreasing
  have numeric := numeric552 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127))
  rw [oldBefore148, at148, literal, oldAfter552, gammaAfter552]
  exact numeric
theorem numeric553 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 148 p
  rw [at148] at beforeRange
  have afterRange := bonus_range 125 (HazardPattern.afterPattern 10000 p (.walk 125))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ∧ bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) ≤ 2 at afterRange
  rw [gammaAfter553] at afterRange
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
theorem local553 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 125) + NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) + bonus 125 (HazardPattern.afterPattern 10000 p (.walk 125)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 125) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) < bonus 148 p at decreasing
  rw [gammaAfter553, at148] at decreasing
  have numeric := numeric553 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125))
  rw [oldBefore148, at148, literal, oldAfter553, gammaAfter553]
  exact numeric
theorem numeric554 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 148 p
  rw [at148] at beforeRange
  have afterRange := bonus_range 171 (HazardPattern.afterPattern 10000 p (.walk 171))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ∧ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ≤ 2 at afterRange
  rw [gammaAfter554] at afterRange
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
theorem local554 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 171) + NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 171))) + bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 171) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 148 p at decreasing
  rw [gammaAfter554, at148] at decreasing
  have numeric := numeric554 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171))
  rw [oldBefore148, at148, literal, oldAfter554, gammaAfter554]
  exact numeric
theorem numeric555 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 148 p
  rw [at148] at beforeRange
  have afterRange := bonus_range 169 (HazardPattern.afterPattern 10000 p (.walk 169))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ∧ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ≤ 2 at afterRange
  rw [gammaAfter555] at afterRange
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
theorem local555 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 169) + NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) + bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 169) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 148 p at decreasing
  rw [gammaAfter555, at148] at decreasing
  have numeric := numeric555 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169))
  rw [oldBefore148, at148, literal, oldAfter555, gammaAfter555]
  exact numeric
theorem numeric556 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 149 p
  rw [at149] at beforeRange
  have afterRange := bonus_range 127 (HazardPattern.afterPattern 10000 p (.walk 127))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ∧ bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) ≤ 2 at afterRange
  rw [gammaAfter556] at afterRange
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
theorem local556 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 149 p) :
    NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 149 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 127) + NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) + bonus 127 (HazardPattern.afterPattern 10000 p (.walk 127)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 127) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) < bonus 149 p at decreasing
  rw [gammaAfter556, at149] at decreasing
  have numeric := numeric556 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127))
  rw [oldBefore149, at149, literal, oldAfter556, gammaAfter556]
  exact numeric
theorem numeric557 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 149 p
  rw [at149] at beforeRange
  have afterRange := bonus_range 127 (HazardPattern.afterPattern 10000 p (.push 127 (.stay 105)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 127 (.stay 105))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 105))) ∧ bonus (HazardPattern.nextHero (.push 127 (.stay 105))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 105))) ≤ 2 at afterRange
  rw [gammaAfter557] at afterRange
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
theorem local557 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 127 (HazardPattern.afterPattern 10000 p (.push 127 (.stay 105))) < bonus 149 p) :
    NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 149 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 127 (.stay 105)) + NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 127 (.stay 105)))) + bonus 127 (HazardPattern.afterPattern 10000 p (.push 127 (.stay 105))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 127 (.stay 105)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 127 (.stay 105))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 105))) < bonus 149 p at decreasing
  rw [gammaAfter557, at149] at decreasing
  have numeric := numeric557 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 127 (.stay 105))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 105)))
  rw [oldBefore149, at149, literal, oldAfter557, gammaAfter557]
  exact numeric
theorem numeric558 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 149 p
  rw [at149] at beforeRange
  have afterRange := bonus_range 171 (HazardPattern.afterPattern 10000 p (.walk 171))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ∧ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ≤ 2 at afterRange
  rw [gammaAfter558] at afterRange
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
theorem local558 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 149 p) :
    NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 149 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 171) + NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 171))) + bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 171) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 149 p at decreasing
  rw [gammaAfter558, at149] at decreasing
  have numeric := numeric558 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171))
  rw [oldBefore149, at149, literal, oldAfter558, gammaAfter558]
  exact numeric
theorem numeric559 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 149 p
  rw [at149] at beforeRange
  have afterRange := bonus_range 171 (HazardPattern.afterPattern 10000 p (.push 171 (.stay 193)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 171 (.stay 193))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 193))) ∧ bonus (HazardPattern.nextHero (.push 171 (.stay 193))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 193))) ≤ 2 at afterRange
  rw [gammaAfter559] at afterRange
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
theorem local559 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 171 (HazardPattern.afterPattern 10000 p (.push 171 (.stay 193))) < bonus 149 p) :
    NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 149 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 171 (.stay 193)) + NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 171 (.stay 193)))) + bonus 171 (HazardPattern.afterPattern 10000 p (.push 171 (.stay 193))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 171 (.stay 193)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 171 (.stay 193))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 193))) < bonus 149 p at decreasing
  rw [gammaAfter559, at149] at decreasing
  have numeric := numeric559 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 171 (.stay 193))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 193)))
  rw [oldBefore149, at149, literal, oldAfter559, gammaAfter559]
  exact numeric
end NetHack.Soko22Hazard87
