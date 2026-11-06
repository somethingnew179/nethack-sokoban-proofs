import NetHack.Soko22Hazard87.Numeric008
import NetHack.Soko22Hazard87.AndIntroBlocks0182
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric630 (p : Pattern) (guard : d128580 p = 1) (decreasing : d0 p < d18533 p) :
    d48547 p + d18533 p ≤ (0 : Int) + d48251 p + d0 p := by
  have beforeRange := bonus_range 161 p
  rw [at161] at beforeRange
  have afterRange := bonus_range 138 (HazardPattern.afterPattern 10000 p (.walk 138))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) ∧ bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) ≤ 2 at afterRange
  rw [gammaAfter630] at afterRange
  have possibilities : (d18533 p = 1 ∧ d0 p = 0) ∨ (d18533 p = 2 ∧ d0 p = 0) ∨ (d18533 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10478 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro41867 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare24103 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro41900 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare24104 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro41900 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare24103 p complete
    omega
theorem local630 (p : Pattern) (guard : d128580 p = 1)
    (decreasing : bonus 138 (HazardPattern.afterPattern 10000 p (.walk 138)) < bonus 161 p) :
    NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 161 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 138) + NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 138))) + bonus 138 (HazardPattern.afterPattern 10000 p (.walk 138)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 138) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) < bonus 161 p at decreasing
  rw [gammaAfter630, at161] at decreasing
  have numeric := numeric630 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138))
  rw [oldBefore161, at161, literal, oldAfter630, gammaAfter630]
  exact numeric
theorem numeric631 (p : Pattern) (guard : d187676 p = 1) (decreasing : d20891 p < d18533 p) :
    d48547 p + d18533 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 161 p
  rw [at161] at beforeRange
  have afterRange := bonus_range 184 (HazardPattern.afterPattern 10000 p (.walk 184))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) ∧ bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) ≤ 2 at afterRange
  rw [gammaAfter631] at afterRange
  have possibilities : (d18533 p = 1 ∧ d20891 p = 0) ∨ (d18533 p = 2 ∧ d20891 p = 0) ∨ (d18533 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10478 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro41905 p beforeEq guard
    have complete := andIntro42017 p afterEq combined
    have bound := compare24105 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro42022 p beforeEq guard
    have complete := andIntro42056 p afterEq combined
    have bound := compare24106 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro42022 p beforeEq guard
    have complete := andIntro42084 p afterEq combined
    have bound := compare24105 p complete
    omega
theorem local631 (p : Pattern) (guard : d187676 p = 1)
    (decreasing : bonus 184 (HazardPattern.afterPattern 10000 p (.walk 184)) < bonus 161 p) :
    NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 161 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 184) + NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 184))) + bonus 184 (HazardPattern.afterPattern 10000 p (.walk 184)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 184) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) < bonus 161 p at decreasing
  rw [gammaAfter631, at161] at decreasing
  have numeric := numeric631 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184))
  rw [oldBefore161, at161, literal, oldAfter631, gammaAfter631]
  exact numeric
theorem numeric632 (p : Pattern) (guard : d187678 p = 1) (decreasing : d17560 p < d18533 p) :
    d48547 p + d18533 p ≤ (0 : Int) + d49280 p + d17560 p := by
  have beforeRange := bonus_range 161 p
  rw [at161] at beforeRange
  have afterRange := bonus_range 182 (HazardPattern.afterPattern 10000 p (.walk 182))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) ∧ bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) ≤ 2 at afterRange
  rw [gammaAfter632] at afterRange
  have possibilities : (d18533 p = 1 ∧ d17560 p = 0) ∨ (d18533 p = 2 ∧ d17560 p = 0) ∨ (d18533 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10478 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro42085 p beforeEq guard
    have complete := andIntro41576 p afterEq combined
    have bound := compare24107 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro42086 p beforeEq guard
    have complete := andIntro41611 p afterEq combined
    have bound := compare24108 p complete
    omega
  · have beforeEq := eqIntro16556 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro42086 p beforeEq guard
    have complete := andIntro41639 p afterEq combined
    have bound := compare24107 p complete
    omega
theorem local632 (p : Pattern) (guard : d187678 p = 1)
    (decreasing : bonus 182 (HazardPattern.afterPattern 10000 p (.walk 182)) < bonus 161 p) :
    NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 161 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 182) + NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 182))) + bonus 182 (HazardPattern.afterPattern 10000 p (.walk 182)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 182) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) < bonus 161 p at decreasing
  rw [gammaAfter632, at161] at decreasing
  have numeric := numeric632 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182))
  rw [oldBefore161, at161, literal, oldAfter632, gammaAfter632]
  exact numeric
theorem numeric633 (p : Pattern) (guard : d187679 p = 1) (decreasing : d20891 p < d19737 p) :
    d48749 p + d19737 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 162 p
  rw [at162] at beforeRange
  have afterRange := bonus_range 184 (HazardPattern.afterPattern 10000 p (.walk 184))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) ∧ bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) ≤ 2 at afterRange
  rw [gammaAfter633] at afterRange
  have possibilities : (d19737 p = 1 ∧ d20891 p = 0) ∨ (d19737 p = 2 ∧ d20891 p = 0) ∨ (d19737 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11224 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro42087 p beforeEq guard
    have complete := andIntro42230 p afterEq combined
    have bound := compare24109 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro42231 p guard beforeEq
    have complete := andIntro42265 p afterEq combined
    have bound := compare24110 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro42231 p guard beforeEq
    have complete := andIntro42293 p afterEq combined
    have bound := compare24109 p complete
    omega
theorem local633 (p : Pattern) (guard : d187679 p = 1)
    (decreasing : bonus 184 (HazardPattern.afterPattern 10000 p (.walk 184)) < bonus 162 p) :
    NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 162 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 184) + NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 184))) + bonus 184 (HazardPattern.afterPattern 10000 p (.walk 184)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 184) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) < bonus 162 p at decreasing
  rw [gammaAfter633, at162] at decreasing
  have numeric := numeric633 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184))
  rw [oldBefore162, at162, literal, oldAfter633, gammaAfter633]
  exact numeric
theorem numeric634 (p : Pattern) (guard : d131098 p = 1) (decreasing : d20389 p < d19737 p) :
    d48749 p + d19737 p ≤ (0 : Int) + d48997 p + d20389 p := by
  have beforeRange := bonus_range 162 p
  rw [at162] at beforeRange
  have afterRange := bonus_range 163 (HazardPattern.afterPattern 10000 p (.walk 163))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) ∧ bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) ≤ 2 at afterRange
  rw [gammaAfter634] at afterRange
  have possibilities : (d19737 p = 1 ∧ d20389 p = 0) ∨ (d19737 p = 2 ∧ d20389 p = 0) ∨ (d19737 p = 2 ∧ d20389 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11224 p pair.1
    have afterEq := eqIntro10791 p pair.2
    have combined := andIntro42405 p guard beforeEq
    have complete := andIntro42486 p afterEq combined
    have bound := compare24111 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro10791 p pair.2
    have combined := andIntro42519 p guard beforeEq
    have complete := andIntro42553 p afterEq combined
    have bound := compare24112 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro10843 p pair.2
    have combined := andIntro42519 p guard beforeEq
    have complete := andIntro42581 p afterEq combined
    have bound := compare24111 p complete
    omega
theorem local634 (p : Pattern) (guard : d131098 p = 1)
    (decreasing : bonus 163 (HazardPattern.afterPattern 10000 p (.walk 163)) < bonus 162 p) :
    NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 162 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 163) + NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 163))) + bonus 163 (HazardPattern.afterPattern 10000 p (.walk 163)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 163) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) < bonus 162 p at decreasing
  rw [gammaAfter634, at162] at decreasing
  have numeric := numeric634 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163))
  rw [oldBefore162, at162, literal, oldAfter634, gammaAfter634]
  exact numeric
theorem numeric635 (p : Pattern) (guard : d188487 p = 1) (decreasing : d0 p < d19737 p) :
    d48749 p + d19737 p ≤ (4 : Int) + d130479 p + d0 p := by
  have beforeRange := bonus_range 162 p
  rw [at162] at beforeRange
  have afterRange := bonus_range 163 (HazardPattern.afterPattern 10000 p (.push 163 (.stay 164)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 163 (.stay 164))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 164))) ∧ bonus (HazardPattern.nextHero (.push 163 (.stay 164))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 164))) ≤ 2 at afterRange
  rw [gammaAfter635] at afterRange
  have possibilities : (d19737 p = 1 ∧ d0 p = 0) ∨ (d19737 p = 2 ∧ d0 p = 0) ∨ (d19737 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11224 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro42724 p beforeEq guard
    have complete := andIntro42725 p afterEq combined
    have bound := compare24922 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro42758 p beforeEq guard
    have complete := andIntro42759 p afterEq combined
    have bound := compare25453 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro42758 p beforeEq guard
    have complete := andIntro42760 p afterEq combined
    have bound := compare24113 p complete
    omega
theorem local635 (p : Pattern) (guard : d188487 p = 1)
    (decreasing : bonus 163 (HazardPattern.afterPattern 10000 p (.push 163 (.stay 164))) < bonus 162 p) :
    NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 162 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 163 (.stay 164)) + NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 163 (.stay 164)))) + bonus 163 (HazardPattern.afterPattern 10000 p (.push 163 (.stay 164))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 163 (.stay 164)) = (4 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 163 (.stay 164))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 164))) < bonus 162 p at decreasing
  rw [gammaAfter635, at162] at decreasing
  have numeric := numeric635 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 163 (.stay 164))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 164)))
  rw [oldBefore162, at162, literal, oldAfter635, gammaAfter635]
  exact numeric
theorem numeric636 (p : Pattern) (guard : d180908 p = 1) (decreasing : d18533 p < d19737 p) :
    d48749 p + d19737 p ≤ (0 : Int) + d48547 p + d18533 p := by
  have beforeRange := bonus_range 162 p
  rw [at162] at beforeRange
  have afterRange := bonus_range 161 (HazardPattern.afterPattern 10000 p (.walk 161))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) ∧ bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) ≤ 2 at afterRange
  rw [gammaAfter636] at afterRange
  have possibilities : (d19737 p = 1 ∧ d18533 p = 0) ∨ (d19737 p = 2 ∧ d18533 p = 0) ∨ (d19737 p = 2 ∧ d18533 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11224 p pair.1
    have afterEq := eqIntro10408 p pair.2
    have combined := andIntro42903 p beforeEq guard
    have complete := andIntro43015 p afterEq combined
    have bound := compare25454 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro10408 p pair.2
    have combined := andIntro43048 p guard beforeEq
    have complete := andIntro43082 p afterEq combined
    have bound := compare25455 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro10478 p pair.2
    have combined := andIntro43048 p guard beforeEq
    have complete := andIntro43110 p afterEq combined
    have bound := compare25454 p complete
    omega
theorem local636 (p : Pattern) (guard : d180908 p = 1)
    (decreasing : bonus 161 (HazardPattern.afterPattern 10000 p (.walk 161)) < bonus 162 p) :
    NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 162 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 161) + NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 161))) + bonus 161 (HazardPattern.afterPattern 10000 p (.walk 161)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 161) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) < bonus 162 p at decreasing
  rw [gammaAfter636, at162] at decreasing
  have numeric := numeric636 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161))
  rw [oldBefore162, at162, literal, oldAfter636, gammaAfter636]
  exact numeric
theorem numeric637 (p : Pattern) (guard : d173704 p = 1) (decreasing : d0 p < d19737 p) :
    d48749 p + d19737 p ≤ (0 : Int) + d188518 p + d0 p := by
  have beforeRange := bonus_range 162 p
  rw [at162] at beforeRange
  have afterRange := bonus_range 161 (HazardPattern.afterPattern 10000 p (.push 161 (.stay 160)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 161 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 161 (.stay 160))) ∧ bonus (HazardPattern.nextHero (.push 161 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 161 (.stay 160))) ≤ 2 at afterRange
  rw [gammaAfter637] at afterRange
  have possibilities : (d19737 p = 1 ∧ d0 p = 0) ∨ (d19737 p = 2 ∧ d0 p = 0) ∨ (d19737 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11224 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro43222 p beforeEq guard
    have complete := andIntro43223 p afterEq combined
    have bound := compare27398 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro43256 p guard beforeEq
    have complete := andIntro43257 p afterEq combined
    have bound := compare28837 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro43256 p guard beforeEq
    have complete := andIntro43258 p afterEq combined
    have bound := compare25456 p complete
    omega
theorem local637 (p : Pattern) (guard : d173704 p = 1)
    (decreasing : bonus 161 (HazardPattern.afterPattern 10000 p (.push 161 (.stay 160))) < bonus 162 p) :
    NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 162 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 161 (.stay 160)) + NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 161 (.stay 160)))) + bonus 161 (HazardPattern.afterPattern 10000 p (.push 161 (.stay 160))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 161 (.stay 160)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 161 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 161 (.stay 160))) < bonus 162 p at decreasing
  rw [gammaAfter637, at162] at decreasing
  have numeric := numeric637 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 161 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 161 (.stay 160)))
  rw [oldBefore162, at162, literal, oldAfter637, gammaAfter637]
  exact numeric
theorem numeric638 (p : Pattern) (guard : d131099 p = 1) (decreasing : d10648 p < d19737 p) :
    d48749 p + d19737 p ≤ (0 : Int) + d48308 p + d10648 p := by
  have beforeRange := bonus_range 162 p
  rw [at162] at beforeRange
  have afterRange := bonus_range 141 (HazardPattern.afterPattern 10000 p (.walk 141))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) ∧ bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) ≤ 2 at afterRange
  rw [gammaAfter638] at afterRange
  have possibilities : (d19737 p = 1 ∧ d10648 p = 0) ∨ (d19737 p = 2 ∧ d10648 p = 0) ∨ (d19737 p = 2 ∧ d10648 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11224 p pair.1
    have afterEq := eqIntro6801 p pair.2
    have combined := andIntro43339 p guard beforeEq
    have complete := andIntro43420 p afterEq combined
    have bound := compare28838 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro6801 p pair.2
    have combined := andIntro43453 p guard beforeEq
    have complete := andIntro43487 p afterEq combined
    have bound := compare28839 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro6896 p pair.2
    have combined := andIntro43453 p guard beforeEq
    have complete := andIntro43515 p afterEq combined
    have bound := compare28838 p complete
    omega
theorem local638 (p : Pattern) (guard : d131099 p = 1)
    (decreasing : bonus 141 (HazardPattern.afterPattern 10000 p (.walk 141)) < bonus 162 p) :
    NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 162 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 141) + NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 141))) + bonus 141 (HazardPattern.afterPattern 10000 p (.walk 141)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 141) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) < bonus 162 p at decreasing
  rw [gammaAfter638, at162] at decreasing
  have numeric := numeric638 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141))
  rw [oldBefore162, at162, literal, oldAfter638, gammaAfter638]
  exact numeric
theorem numeric639 (p : Pattern) (guard : d188524 p = 1) (decreasing : d20891 p < d19737 p) :
    d48749 p + d19737 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 162 p
  rw [at162] at beforeRange
  have afterRange := bonus_range 185 (HazardPattern.afterPattern 10000 p (.walk 185))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) ∧ bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) ≤ 2 at afterRange
  rw [gammaAfter639] at afterRange
  have possibilities : (d19737 p = 1 ∧ d20891 p = 0) ∨ (d19737 p = 2 ∧ d20891 p = 0) ∨ (d19737 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11224 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro43516 p beforeEq guard
    have complete := andIntro42230 p afterEq combined
    have bound := compare24109 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro43517 p beforeEq guard
    have complete := andIntro42265 p afterEq combined
    have bound := compare24110 p complete
    omega
  · have beforeEq := eqIntro17365 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro43517 p beforeEq guard
    have complete := andIntro42293 p afterEq combined
    have bound := compare24109 p complete
    omega
theorem local639 (p : Pattern) (guard : d188524 p = 1)
    (decreasing : bonus 185 (HazardPattern.afterPattern 10000 p (.walk 185)) < bonus 162 p) :
    NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 162 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 185) + NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 185))) + bonus 185 (HazardPattern.afterPattern 10000 p (.walk 185)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 185) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) < bonus 162 p at decreasing
  rw [gammaAfter639, at162] at decreasing
  have numeric := numeric639 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185))
  rw [oldBefore162, at162, literal, oldAfter639, gammaAfter639]
  exact numeric
theorem numeric640 (p : Pattern) (guard : d129672 p = 1) (decreasing : d10648 p < d20389 p) :
    d48997 p + d20389 p ≤ (0 : Int) + d48308 p + d10648 p := by
  have beforeRange := bonus_range 163 p
  rw [at163] at beforeRange
  have afterRange := bonus_range 141 (HazardPattern.afterPattern 10000 p (.walk 141))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) ∧ bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) ≤ 2 at afterRange
  rw [gammaAfter640] at afterRange
  have possibilities : (d20389 p = 1 ∧ d10648 p = 0) ∨ (d20389 p = 2 ∧ d10648 p = 0) ∨ (d20389 p = 2 ∧ d10648 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10843 p pair.1
    have afterEq := eqIntro6801 p pair.2
    have combined := andIntro43598 p guard beforeEq
    have complete := andIntro43679 p afterEq combined
    have bound := compare28840 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro6801 p pair.2
    have combined := andIntro43712 p guard beforeEq
    have complete := andIntro43746 p afterEq combined
    have bound := compare28841 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro6896 p pair.2
    have combined := andIntro43712 p guard beforeEq
    have complete := andIntro43774 p afterEq combined
    have bound := compare28840 p complete
    omega
theorem local640 (p : Pattern) (guard : d129672 p = 1)
    (decreasing : bonus 141 (HazardPattern.afterPattern 10000 p (.walk 141)) < bonus 163 p) :
    NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 163 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 141) + NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 141))) + bonus 141 (HazardPattern.afterPattern 10000 p (.walk 141)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 141) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) < bonus 163 p at decreasing
  rw [gammaAfter640, at163] at decreasing
  have numeric := numeric640 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141))
  rw [oldBefore163, at163, literal, oldAfter640, gammaAfter640]
  exact numeric
theorem numeric641 (p : Pattern) (guard : d102055 p = 1) (decreasing : d189322 p < d20389 p) :
    d48997 p + d20389 p ≤ (2 : Int) + d188744 p + d189322 p := by
  have beforeRange := bonus_range 163 p
  rw [at163] at beforeRange
  have afterRange := bonus_range 141 (HazardPattern.afterPattern 10000 p (.push 141 (.stay 119)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 141 (.stay 119))) (HazardPattern.afterPattern 10000 p (.push 141 (.stay 119))) ∧ bonus (HazardPattern.nextHero (.push 141 (.stay 119))) (HazardPattern.afterPattern 10000 p (.push 141 (.stay 119))) ≤ 2 at afterRange
  rw [gammaAfter641] at afterRange
  have possibilities : (d20389 p = 1 ∧ d189322 p = 0) ∨ (d20389 p = 2 ∧ d189322 p = 0) ∨ (d20389 p = 2 ∧ d189322 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10843 p pair.1
    have afterEq := eqIntro17575 p pair.2
    have combined := andIntro43855 p guard beforeEq
    have complete := andIntro43936 p afterEq combined
    have bound := compare28842 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro17575 p pair.2
    have combined := andIntro43969 p guard beforeEq
    have complete := andIntro44003 p afterEq combined
    have bound := compare28843 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro17627 p pair.2
    have combined := andIntro43969 p guard beforeEq
    have complete := andIntro44031 p combined afterEq
    have bound := compare28842 p complete
    omega
theorem local641 (p : Pattern) (guard : d102055 p = 1)
    (decreasing : bonus 141 (HazardPattern.afterPattern 10000 p (.push 141 (.stay 119))) < bonus 163 p) :
    NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 163 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 141 (.stay 119)) + NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 141 (.stay 119)))) + bonus 141 (HazardPattern.afterPattern 10000 p (.push 141 (.stay 119))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 141 (.stay 119)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 141 (.stay 119))) (HazardPattern.afterPattern 10000 p (.push 141 (.stay 119))) < bonus 163 p at decreasing
  rw [gammaAfter641, at163] at decreasing
  have numeric := numeric641 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 141 (.stay 119))) (HazardPattern.afterPattern 10000 p (.push 141 (.stay 119)))
  rw [oldBefore163, at163, literal, oldAfter641, gammaAfter641]
  exact numeric
theorem numeric642 (p : Pattern) (guard : d190593 p = 1) (decreasing : d20891 p < d20389 p) :
    d48997 p + d20389 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 163 p
  rw [at163] at beforeRange
  have afterRange := bonus_range 185 (HazardPattern.afterPattern 10000 p (.walk 185))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) ∧ bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) ≤ 2 at afterRange
  rw [gammaAfter642] at afterRange
  have possibilities : (d20389 p = 1 ∧ d20891 p = 0) ∨ (d20389 p = 2 ∧ d20891 p = 0) ∨ (d20389 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10843 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro44032 p beforeEq guard
    have complete := andIntro44144 p combined afterEq
    have bound := compare28844 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro44145 p beforeEq guard
    have complete := andIntro44179 p afterEq combined
    have bound := compare28845 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro44145 p beforeEq guard
    have complete := andIntro44207 p afterEq combined
    have bound := compare28844 p complete
    omega
theorem local642 (p : Pattern) (guard : d190593 p = 1)
    (decreasing : bonus 185 (HazardPattern.afterPattern 10000 p (.walk 185)) < bonus 163 p) :
    NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 163 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 185) + NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 185))) + bonus 185 (HazardPattern.afterPattern 10000 p (.walk 185)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 185) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) < bonus 163 p at decreasing
  rw [gammaAfter642, at163] at decreasing
  have numeric := numeric642 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185))
  rw [oldBefore163, at163, literal, oldAfter642, gammaAfter642]
  exact numeric
theorem numeric643 (p : Pattern) (guard : d190594 p = 1) (decreasing : d20891 p < d20389 p) :
    d48997 p + d20389 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 163 p
  rw [at163] at beforeRange
  have afterRange := bonus_range 164 (HazardPattern.afterPattern 10000 p (.walk 164))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) ∧ bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) ≤ 2 at afterRange
  rw [gammaAfter643] at afterRange
  have possibilities : (d20389 p = 1 ∧ d20891 p = 0) ∨ (d20389 p = 2 ∧ d20891 p = 0) ∨ (d20389 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10843 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro44208 p beforeEq guard
    have complete := andIntro44144 p combined afterEq
    have bound := compare28844 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro44209 p beforeEq guard
    have complete := andIntro44179 p afterEq combined
    have bound := compare28845 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro44209 p beforeEq guard
    have complete := andIntro44207 p afterEq combined
    have bound := compare28844 p complete
    omega
theorem local643 (p : Pattern) (guard : d190594 p = 1)
    (decreasing : bonus 164 (HazardPattern.afterPattern 10000 p (.walk 164)) < bonus 163 p) :
    NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 163 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 164) + NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 164))) + bonus 164 (HazardPattern.afterPattern 10000 p (.walk 164)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 164) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) < bonus 163 p at decreasing
  rw [gammaAfter643, at163] at decreasing
  have numeric := numeric643 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164))
  rw [oldBefore163, at163, literal, oldAfter643, gammaAfter643]
  exact numeric
theorem numeric644 (p : Pattern) (guard : d131098 p = 1) (decreasing : d19737 p < d20389 p) :
    d48997 p + d20389 p ≤ (0 : Int) + d48749 p + d19737 p := by
  have beforeRange := bonus_range 163 p
  rw [at163] at beforeRange
  have afterRange := bonus_range 162 (HazardPattern.afterPattern 10000 p (.walk 162))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) ∧ bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) ≤ 2 at afterRange
  rw [gammaAfter644] at afterRange
  have possibilities : (d20389 p = 1 ∧ d19737 p = 0) ∨ (d20389 p = 2 ∧ d19737 p = 0) ∨ (d20389 p = 2 ∧ d19737 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10843 p pair.1
    have afterEq := eqIntro11154 p pair.2
    have combined := andIntro44290 p beforeEq guard
    have complete := andIntro44402 p afterEq combined
    have bound := compare28846 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro11154 p pair.2
    have combined := andIntro44435 p guard beforeEq
    have complete := andIntro44469 p afterEq combined
    have bound := compare28847 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro11224 p pair.2
    have combined := andIntro44435 p guard beforeEq
    have complete := andIntro44497 p afterEq combined
    have bound := compare28846 p complete
    omega
theorem local644 (p : Pattern) (guard : d131098 p = 1)
    (decreasing : bonus 162 (HazardPattern.afterPattern 10000 p (.walk 162)) < bonus 163 p) :
    NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 163 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 162) + NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 162))) + bonus 162 (HazardPattern.afterPattern 10000 p (.walk 162)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 162) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) < bonus 163 p at decreasing
  rw [gammaAfter644, at163] at decreasing
  have numeric := numeric644 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162))
  rw [oldBefore163, at163, literal, oldAfter644, gammaAfter644]
  exact numeric
theorem numeric645 (p : Pattern) (guard : d181811 p = 1) (decreasing : d191282 p < d20389 p) :
    d48997 p + d20389 p ≤ (0 : Int) + d190630 p + d191282 p := by
  have beforeRange := bonus_range 163 p
  rw [at163] at beforeRange
  have afterRange := bonus_range 162 (HazardPattern.afterPattern 10000 p (.push 162 (.stay 161)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 162 (.stay 161))) (HazardPattern.afterPattern 10000 p (.push 162 (.stay 161))) ∧ bonus (HazardPattern.nextHero (.push 162 (.stay 161))) (HazardPattern.afterPattern 10000 p (.push 162 (.stay 161))) ≤ 2 at afterRange
  rw [gammaAfter645] at afterRange
  have possibilities : (d20389 p = 1 ∧ d191282 p = 0) ∨ (d20389 p = 2 ∧ d191282 p = 0) ∨ (d20389 p = 2 ∧ d191282 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10843 p pair.1
    have afterEq := eqIntro17732 p pair.2
    have combined := andIntro44609 p beforeEq guard
    have complete := andIntro44721 p afterEq combined
    have bound := compare28848 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro17732 p pair.2
    have combined := andIntro44754 p guard beforeEq
    have complete := andIntro44788 p afterEq combined
    have bound := compare28849 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro17784 p pair.2
    have combined := andIntro44754 p guard beforeEq
    have complete := andIntro44816 p combined afterEq
    have bound := compare28848 p complete
    omega
theorem local645 (p : Pattern) (guard : d181811 p = 1)
    (decreasing : bonus 162 (HazardPattern.afterPattern 10000 p (.push 162 (.stay 161))) < bonus 163 p) :
    NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 163 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 162 (.stay 161)) + NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 162 (.stay 161)))) + bonus 162 (HazardPattern.afterPattern 10000 p (.push 162 (.stay 161))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 162 (.stay 161)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 162 (.stay 161))) (HazardPattern.afterPattern 10000 p (.push 162 (.stay 161))) < bonus 163 p at decreasing
  rw [gammaAfter645, at163] at decreasing
  have numeric := numeric645 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 162 (.stay 161))) (HazardPattern.afterPattern 10000 p (.push 162 (.stay 161)))
  rw [oldBefore163, at163, literal, oldAfter645, gammaAfter645]
  exact numeric
theorem numeric646 (p : Pattern) (guard : d192712 p = 1) (decreasing : d20891 p < d20389 p) :
    d48997 p + d20389 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 163 p
  rw [at163] at beforeRange
  have afterRange := bonus_range 186 (HazardPattern.afterPattern 10000 p (.walk 186))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186)) ∧ bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186)) ≤ 2 at afterRange
  rw [gammaAfter646] at afterRange
  have possibilities : (d20389 p = 1 ∧ d20891 p = 0) ∨ (d20389 p = 2 ∧ d20891 p = 0) ∨ (d20389 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10843 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro44817 p beforeEq guard
    have complete := andIntro44144 p combined afterEq
    have bound := compare28844 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro44818 p beforeEq guard
    have complete := andIntro44179 p afterEq combined
    have bound := compare28845 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro44818 p beforeEq guard
    have complete := andIntro44207 p afterEq combined
    have bound := compare28844 p complete
    omega
theorem local646 (p : Pattern) (guard : d192712 p = 1)
    (decreasing : bonus 186 (HazardPattern.afterPattern 10000 p (.walk 186)) < bonus 163 p) :
    NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 163 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 186) + NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 186))) + bonus 186 (HazardPattern.afterPattern 10000 p (.walk 186)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 186) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186)) < bonus 163 p at decreasing
  rw [gammaAfter646, at163] at decreasing
  have numeric := numeric646 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186))
  rw [oldBefore163, at163, literal, oldAfter646, gammaAfter646]
  exact numeric
theorem numeric647 (p : Pattern) (guard : d192716 p = 1) (decreasing : d20891 p < d20389 p) :
    d48997 p + d20389 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 163 p
  rw [at163] at beforeRange
  have afterRange := bonus_range 184 (HazardPattern.afterPattern 10000 p (.walk 184))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) ∧ bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) ≤ 2 at afterRange
  rw [gammaAfter647] at afterRange
  have possibilities : (d20389 p = 1 ∧ d20891 p = 0) ∨ (d20389 p = 2 ∧ d20891 p = 0) ∨ (d20389 p = 2 ∧ d20891 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro10843 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro44819 p beforeEq guard
    have complete := andIntro44144 p combined afterEq
    have bound := compare28844 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro10948 p pair.2
    have combined := andIntro44820 p beforeEq guard
    have complete := andIntro44179 p afterEq combined
    have bound := compare28845 p complete
    omega
  · have beforeEq := eqIntro17470 p pair.1
    have afterEq := eqIntro11000 p pair.2
    have combined := andIntro44820 p beforeEq guard
    have complete := andIntro44207 p afterEq combined
    have bound := compare28844 p complete
    omega
theorem local647 (p : Pattern) (guard : d192716 p = 1)
    (decreasing : bonus 184 (HazardPattern.afterPattern 10000 p (.walk 184)) < bonus 163 p) :
    NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 163 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 184) + NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 184))) + bonus 184 (HazardPattern.afterPattern 10000 p (.walk 184)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 184) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) < bonus 163 p at decreasing
  rw [gammaAfter647, at163] at decreasing
  have numeric := numeric647 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184))
  rw [oldBefore163, at163, literal, oldAfter647, gammaAfter647]
  exact numeric
theorem numeric648 (p : Pattern) (guard : d192717 p = 1) (decreasing : d20891 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 164 p
  rw [at164] at beforeRange
  have afterRange := bonus_range 186 (HazardPattern.afterPattern 10000 p (.walk 186))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186)) ∧ bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186)) ≤ 2 at afterRange
  rw [gammaAfter648] at afterRange
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
theorem local648 (p : Pattern) (guard : d192717 p = 1)
    (decreasing : bonus 186 (HazardPattern.afterPattern 10000 p (.walk 186)) < bonus 164 p) :
    NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 164 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 186) + NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 186))) + bonus 186 (HazardPattern.afterPattern 10000 p (.walk 186)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 186) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186)) < bonus 164 p at decreasing
  rw [gammaAfter648, at164] at decreasing
  have numeric := numeric648 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186))
  rw [oldBefore164, at164, literal, oldAfter648, gammaAfter648]
  exact numeric
theorem numeric649 (p : Pattern) (guard : d190594 p = 1) (decreasing : d20389 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d48997 p + d20389 p := by
  have beforeRange := bonus_range 164 p
  rw [at164] at beforeRange
  have afterRange := bonus_range 163 (HazardPattern.afterPattern 10000 p (.walk 163))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) ∧ bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) ≤ 2 at afterRange
  rw [gammaAfter649] at afterRange
  have possibilities : (d20891 p = 1 ∧ d20389 p = 0) ∨ (d20891 p = 2 ∧ d20389 p = 0) ∨ (d20891 p = 2 ∧ d20389 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro10791 p pair.2
    have combined := andIntro45077 p beforeEq guard
    have complete := andIntro45158 p afterEq combined
    have bound := compare28852 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10791 p pair.2
    have combined := andIntro45191 p guard beforeEq
    have complete := andIntro45225 p afterEq combined
    have bound := compare28853 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10843 p pair.2
    have combined := andIntro45191 p guard beforeEq
    have complete := andIntro45253 p afterEq combined
    have bound := compare28852 p complete
    omega
theorem local649 (p : Pattern) (guard : d190594 p = 1)
    (decreasing : bonus 163 (HazardPattern.afterPattern 10000 p (.walk 163)) < bonus 164 p) :
    NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 164 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 163) + NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 163))) + bonus 163 (HazardPattern.afterPattern 10000 p (.walk 163)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 163) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) < bonus 164 p at decreasing
  rw [gammaAfter649, at164] at decreasing
  have numeric := numeric649 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163))
  rw [oldBefore164, at164, literal, oldAfter649, gammaAfter649]
  exact numeric
theorem numeric650 (p : Pattern) (guard : d188487 p = 1) (decreasing : d193613 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d192961 p + d193613 p := by
  have beforeRange := bonus_range 164 p
  rw [at164] at beforeRange
  have afterRange := bonus_range 163 (HazardPattern.afterPattern 10000 p (.push 163 (.stay 162)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 163 (.stay 162))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 162))) ∧ bonus (HazardPattern.nextHero (.push 163 (.stay 162))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 162))) ≤ 2 at afterRange
  rw [gammaAfter650] at afterRange
  have possibilities : (d20891 p = 1 ∧ d193613 p = 0) ∨ (d20891 p = 2 ∧ d193613 p = 0) ∨ (d20891 p = 2 ∧ d193613 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro17994 p pair.2
    have combined := andIntro45396 p beforeEq guard
    have complete := andIntro45508 p combined afterEq
    have bound := compare28854 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro17994 p pair.2
    have combined := andIntro45541 p guard beforeEq
    have complete := andIntro45575 p combined afterEq
    have bound := compare28855 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro18046 p pair.2
    have combined := andIntro45541 p guard beforeEq
    have complete := andIntro45603 p combined afterEq
    have bound := compare28854 p complete
    omega
theorem local650 (p : Pattern) (guard : d188487 p = 1)
    (decreasing : bonus 163 (HazardPattern.afterPattern 10000 p (.push 163 (.stay 162))) < bonus 164 p) :
    NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 164 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 163 (.stay 162)) + NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 163 (.stay 162)))) + bonus 163 (HazardPattern.afterPattern 10000 p (.push 163 (.stay 162))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 163 (.stay 162)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 163 (.stay 162))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 162))) < bonus 164 p at decreasing
  rw [gammaAfter650, at164] at decreasing
  have numeric := numeric650 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 163 (.stay 162))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 162)))
  rw [oldBefore164, at164, literal, oldAfter650, gammaAfter650]
  exact numeric
theorem numeric651 (p : Pattern) (guard : d130482 p = 1) (decreasing : d10648 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d48308 p + d10648 p := by
  have beforeRange := bonus_range 164 p
  rw [at164] at beforeRange
  have afterRange := bonus_range 141 (HazardPattern.afterPattern 10000 p (.walk 141))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) ∧ bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) ≤ 2 at afterRange
  rw [gammaAfter651] at afterRange
  have possibilities : (d20891 p = 1 ∧ d10648 p = 0) ∨ (d20891 p = 2 ∧ d10648 p = 0) ∨ (d20891 p = 2 ∧ d10648 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro6801 p pair.2
    have combined := andIntro45684 p guard beforeEq
    have complete := andIntro43679 p afterEq combined
    have bound := compare28856 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro6801 p pair.2
    have combined := andIntro45717 p guard beforeEq
    have complete := andIntro43746 p afterEq combined
    have bound := compare28857 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro6896 p pair.2
    have combined := andIntro45717 p guard beforeEq
    have complete := andIntro43774 p afterEq combined
    have bound := compare28856 p complete
    omega
theorem local651 (p : Pattern) (guard : d130482 p = 1)
    (decreasing : bonus 141 (HazardPattern.afterPattern 10000 p (.walk 141)) < bonus 164 p) :
    NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 164 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 141) + NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 141))) + bonus 141 (HazardPattern.afterPattern 10000 p (.walk 141)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 141) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) < bonus 164 p at decreasing
  rw [gammaAfter651, at164] at decreasing
  have numeric := numeric651 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141))
  rw [oldBefore164, at164, literal, oldAfter651, gammaAfter651]
  exact numeric
theorem numeric652 (p : Pattern) (guard : d194332 p = 1) (decreasing : d20891 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d49102 p + d20891 p := by
  have beforeRange := bonus_range 164 p
  rw [at164] at beforeRange
  have afterRange := bonus_range 185 (HazardPattern.afterPattern 10000 p (.walk 185))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) ∧ bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) ≤ 2 at afterRange
  rw [gammaAfter652] at afterRange
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
theorem local652 (p : Pattern) (guard : d194332 p = 1)
    (decreasing : bonus 185 (HazardPattern.afterPattern 10000 p (.walk 185)) < bonus 164 p) :
    NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 164 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 185) + NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 185))) + bonus 185 (HazardPattern.afterPattern 10000 p (.walk 185)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 185) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) < bonus 164 p at decreasing
  rw [gammaAfter652, at164] at decreasing
  have numeric := numeric652 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185))
  rw [oldBefore164, at164, literal, oldAfter652, gammaAfter652]
  exact numeric
theorem numeric653 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 166 p
  rw [at166] at beforeRange
  have afterRange := bonus_range 144 (HazardPattern.afterPattern 10000 p (.walk 144))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) ∧ bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) ≤ 2 at afterRange
  rw [gammaAfter653] at afterRange
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
theorem local653 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 144 (HazardPattern.afterPattern 10000 p (.walk 144)) < bonus 166 p) :
    NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 166 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 144) + NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 144))) + bonus 144 (HazardPattern.afterPattern 10000 p (.walk 144)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 144) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) < bonus 166 p at decreasing
  rw [gammaAfter653, at166] at decreasing
  have numeric := numeric653 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144))
  rw [oldBefore166, at166, literal, oldAfter653, gammaAfter653]
  exact numeric
theorem numeric654 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 166 p
  rw [at166] at beforeRange
  have afterRange := bonus_range 144 (HazardPattern.afterPattern 10000 p (.push 144 (.stay 122)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 144 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 144 (.stay 122))) ∧ bonus (HazardPattern.nextHero (.push 144 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 144 (.stay 122))) ≤ 2 at afterRange
  rw [gammaAfter654] at afterRange
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
theorem local654 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 144 (HazardPattern.afterPattern 10000 p (.push 144 (.stay 122))) < bonus 166 p) :
    NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 166 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 144 (.stay 122)) + NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 144 (.stay 122)))) + bonus 144 (HazardPattern.afterPattern 10000 p (.push 144 (.stay 122))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 144 (.stay 122)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 144 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 144 (.stay 122))) < bonus 166 p at decreasing
  rw [gammaAfter654, at166] at decreasing
  have numeric := numeric654 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 144 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 144 (.stay 122)))
  rw [oldBefore166, at166, literal, oldAfter654, gammaAfter654]
  exact numeric
theorem numeric655 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 166 p
  rw [at166] at beforeRange
  have afterRange := bonus_range 188 (HazardPattern.afterPattern 10000 p (.walk 188))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) ∧ bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) ≤ 2 at afterRange
  rw [gammaAfter655] at afterRange
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
theorem local655 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 188 (HazardPattern.afterPattern 10000 p (.walk 188)) < bonus 166 p) :
    NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 166 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 188) + NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 188))) + bonus 188 (HazardPattern.afterPattern 10000 p (.walk 188)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 188) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) < bonus 166 p at decreasing
  rw [gammaAfter655, at166] at decreasing
  have numeric := numeric655 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188))
  rw [oldBefore166, at166, literal, oldAfter655, gammaAfter655]
  exact numeric
theorem numeric656 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 166 p
  rw [at166] at beforeRange
  have afterRange := bonus_range 188 (HazardPattern.afterPattern 10000 p (.push 188 (.stay 210)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 188 (.stay 210))) (HazardPattern.afterPattern 10000 p (.push 188 (.stay 210))) ∧ bonus (HazardPattern.nextHero (.push 188 (.stay 210))) (HazardPattern.afterPattern 10000 p (.push 188 (.stay 210))) ≤ 2 at afterRange
  rw [gammaAfter656] at afterRange
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
theorem local656 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 188 (HazardPattern.afterPattern 10000 p (.push 188 (.stay 210))) < bonus 166 p) :
    NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 166 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 188 (.stay 210)) + NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 188 (.stay 210)))) + bonus 188 (HazardPattern.afterPattern 10000 p (.push 188 (.stay 210))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 188 (.stay 210)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 188 (.stay 210))) (HazardPattern.afterPattern 10000 p (.push 188 (.stay 210))) < bonus 166 p at decreasing
  rw [gammaAfter656, at166] at decreasing
  have numeric := numeric656 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 188 (.stay 210))) (HazardPattern.afterPattern 10000 p (.push 188 (.stay 210)))
  rw [oldBefore166, at166, literal, oldAfter656, gammaAfter656]
  exact numeric
theorem numeric657 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 166 p
  rw [at166] at beforeRange
  have afterRange := bonus_range 167 (HazardPattern.afterPattern 10000 p (.walk 167))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ∧ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ≤ 2 at afterRange
  rw [gammaAfter657] at afterRange
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
theorem local657 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 166 p) :
    NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 166 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 167) + NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) + bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 167) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 166 p at decreasing
  rw [gammaAfter657, at166] at decreasing
  have numeric := numeric657 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167))
  rw [oldBefore166, at166, literal, oldAfter657, gammaAfter657]
  exact numeric
theorem numeric658 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 166 p
  rw [at166] at beforeRange
  have afterRange := bonus_range 167 (HazardPattern.afterPattern 10000 p (.push 167 (.stay 168)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 167 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 168))) ∧ bonus (HazardPattern.nextHero (.push 167 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 168))) ≤ 2 at afterRange
  rw [gammaAfter658] at afterRange
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
theorem local658 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 167 (HazardPattern.afterPattern 10000 p (.push 167 (.stay 168))) < bonus 166 p) :
    NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 166 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 167 (.stay 168)) + NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 167 (.stay 168)))) + bonus 167 (HazardPattern.afterPattern 10000 p (.push 167 (.stay 168))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 167 (.stay 168)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 167 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 168))) < bonus 166 p at decreasing
  rw [gammaAfter658, at166] at decreasing
  have numeric := numeric658 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 167 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 168)))
  rw [oldBefore166, at166, literal, oldAfter658, gammaAfter658]
  exact numeric
theorem numeric659 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 166 p
  rw [at166] at beforeRange
  have afterRange := bonus_range 145 (HazardPattern.afterPattern 10000 p (.walk 145))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ∧ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ≤ 2 at afterRange
  rw [gammaAfter659] at afterRange
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
theorem local659 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 166 p) :
    NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 166 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 145) + NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) + bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 145) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 166 p at decreasing
  rw [gammaAfter659, at166] at decreasing
  have numeric := numeric659 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145))
  rw [oldBefore166, at166, literal, oldAfter659, gammaAfter659]
  exact numeric
theorem numeric660 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 166 p
  rw [at166] at beforeRange
  have afterRange := bonus_range 189 (HazardPattern.afterPattern 10000 p (.walk 189))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ∧ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ≤ 2 at afterRange
  rw [gammaAfter660] at afterRange
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
theorem local660 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 166 p) :
    NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 166 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 189) + NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 189))) + bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 189) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 166 p at decreasing
  rw [gammaAfter660, at166] at decreasing
  have numeric := numeric660 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189))
  rw [oldBefore166, at166, literal, oldAfter660, gammaAfter660]
  exact numeric
theorem numeric661 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 167 p
  rw [at167] at beforeRange
  have afterRange := bonus_range 145 (HazardPattern.afterPattern 10000 p (.walk 145))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ∧ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ≤ 2 at afterRange
  rw [gammaAfter661] at afterRange
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
theorem local661 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 167 p) :
    NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 167 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 145) + NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) + bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 145) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 167 p at decreasing
  rw [gammaAfter661, at167] at decreasing
  have numeric := numeric661 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145))
  rw [oldBefore167, at167, literal, oldAfter661, gammaAfter661]
  exact numeric
theorem numeric662 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 167 p
  rw [at167] at beforeRange
  have afterRange := bonus_range 145 (HazardPattern.afterPattern 10000 p (.push 145 (.stay 123)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 145 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 123))) ∧ bonus (HazardPattern.nextHero (.push 145 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 123))) ≤ 2 at afterRange
  rw [gammaAfter662] at afterRange
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
theorem local662 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 145 (HazardPattern.afterPattern 10000 p (.push 145 (.stay 123))) < bonus 167 p) :
    NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 167 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 145 (.stay 123)) + NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 145 (.stay 123)))) + bonus 145 (HazardPattern.afterPattern 10000 p (.push 145 (.stay 123))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 145 (.stay 123)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 145 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 123))) < bonus 167 p at decreasing
  rw [gammaAfter662, at167] at decreasing
  have numeric := numeric662 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 145 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 123)))
  rw [oldBefore167, at167, literal, oldAfter662, gammaAfter662]
  exact numeric
theorem numeric663 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 167 p
  rw [at167] at beforeRange
  have afterRange := bonus_range 189 (HazardPattern.afterPattern 10000 p (.walk 189))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ∧ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ≤ 2 at afterRange
  rw [gammaAfter663] at afterRange
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
theorem local663 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 167 p) :
    NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 167 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 189) + NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 189))) + bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 189) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 167 p at decreasing
  rw [gammaAfter663, at167] at decreasing
  have numeric := numeric663 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189))
  rw [oldBefore167, at167, literal, oldAfter663, gammaAfter663]
  exact numeric
theorem numeric664 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 167 p
  rw [at167] at beforeRange
  have afterRange := bonus_range 189 (HazardPattern.afterPattern 10000 p (.push 189 (.stay 211)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 189 (.stay 211))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 211))) ∧ bonus (HazardPattern.nextHero (.push 189 (.stay 211))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 211))) ≤ 2 at afterRange
  rw [gammaAfter664] at afterRange
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
theorem local664 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 189 (HazardPattern.afterPattern 10000 p (.push 189 (.stay 211))) < bonus 167 p) :
    NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 167 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 189 (.stay 211)) + NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 189 (.stay 211)))) + bonus 189 (HazardPattern.afterPattern 10000 p (.push 189 (.stay 211))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 189 (.stay 211)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 189 (.stay 211))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 211))) < bonus 167 p at decreasing
  rw [gammaAfter664, at167] at decreasing
  have numeric := numeric664 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 189 (.stay 211))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 211)))
  rw [oldBefore167, at167, literal, oldAfter664, gammaAfter664]
  exact numeric
theorem numeric665 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 167 p
  rw [at167] at beforeRange
  have afterRange := bonus_range 168 (HazardPattern.afterPattern 10000 p (.walk 168))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ∧ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ≤ 2 at afterRange
  rw [gammaAfter665] at afterRange
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
theorem local665 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 167 p) :
    NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 167 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 168) + NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) + bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 168) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 167 p at decreasing
  rw [gammaAfter665, at167] at decreasing
  have numeric := numeric665 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168))
  rw [oldBefore167, at167, literal, oldAfter665, gammaAfter665]
  exact numeric
theorem numeric666 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 167 p
  rw [at167] at beforeRange
  have afterRange := bonus_range 168 (HazardPattern.afterPattern 10000 p (.push 168 (.stay 169)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 168 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 169))) ∧ bonus (HazardPattern.nextHero (.push 168 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 169))) ≤ 2 at afterRange
  rw [gammaAfter666] at afterRange
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
theorem local666 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 168 (HazardPattern.afterPattern 10000 p (.push 168 (.stay 169))) < bonus 167 p) :
    NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 167 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 168 (.stay 169)) + NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 168 (.stay 169)))) + bonus 168 (HazardPattern.afterPattern 10000 p (.push 168 (.stay 169))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 168 (.stay 169)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 168 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 169))) < bonus 167 p at decreasing
  rw [gammaAfter666, at167] at decreasing
  have numeric := numeric666 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 168 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 169)))
  rw [oldBefore167, at167, literal, oldAfter666, gammaAfter666]
  exact numeric
theorem numeric667 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 167 p
  rw [at167] at beforeRange
  have afterRange := bonus_range 166 (HazardPattern.afterPattern 10000 p (.walk 166))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) ∧ bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) ≤ 2 at afterRange
  rw [gammaAfter667] at afterRange
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
theorem local667 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 166 (HazardPattern.afterPattern 10000 p (.walk 166)) < bonus 167 p) :
    NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 167 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 166) + NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 166))) + bonus 166 (HazardPattern.afterPattern 10000 p (.walk 166)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 166) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) < bonus 167 p at decreasing
  rw [gammaAfter667, at167] at decreasing
  have numeric := numeric667 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166))
  rw [oldBefore167, at167, literal, oldAfter667, gammaAfter667]
  exact numeric
theorem numeric668 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 167 p
  rw [at167] at beforeRange
  have afterRange := bonus_range 146 (HazardPattern.afterPattern 10000 p (.walk 146))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ∧ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ≤ 2 at afterRange
  rw [gammaAfter668] at afterRange
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
theorem local668 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 167 p) :
    NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 167 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 146) + NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) + bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 146) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 167 p at decreasing
  rw [gammaAfter668, at167] at decreasing
  have numeric := numeric668 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146))
  rw [oldBefore167, at167, literal, oldAfter668, gammaAfter668]
  exact numeric
theorem numeric669 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 167 p
  rw [at167] at beforeRange
  have afterRange := bonus_range 144 (HazardPattern.afterPattern 10000 p (.walk 144))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) ∧ bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) ≤ 2 at afterRange
  rw [gammaAfter669] at afterRange
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
theorem local669 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 144 (HazardPattern.afterPattern 10000 p (.walk 144)) < bonus 167 p) :
    NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 167 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 144) + NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 144))) + bonus 144 (HazardPattern.afterPattern 10000 p (.walk 144)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 144) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) < bonus 167 p at decreasing
  rw [gammaAfter669, at167] at decreasing
  have numeric := numeric669 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144))
  rw [oldBefore167, at167, literal, oldAfter669, gammaAfter669]
  exact numeric
theorem numeric670 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 167 p
  rw [at167] at beforeRange
  have afterRange := bonus_range 190 (HazardPattern.afterPattern 10000 p (.walk 190))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ∧ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ≤ 2 at afterRange
  rw [gammaAfter670] at afterRange
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
theorem local670 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 167 p) :
    NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 167 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 190) + NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 190))) + bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 190) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 167 p at decreasing
  rw [gammaAfter670, at167] at decreasing
  have numeric := numeric670 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190))
  rw [oldBefore167, at167, literal, oldAfter670, gammaAfter670]
  exact numeric
theorem numeric671 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 167 p
  rw [at167] at beforeRange
  have afterRange := bonus_range 188 (HazardPattern.afterPattern 10000 p (.walk 188))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) ∧ bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) ≤ 2 at afterRange
  rw [gammaAfter671] at afterRange
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
theorem local671 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 188 (HazardPattern.afterPattern 10000 p (.walk 188)) < bonus 167 p) :
    NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 167 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 188) + NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 188))) + bonus 188 (HazardPattern.afterPattern 10000 p (.walk 188)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 188) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) < bonus 167 p at decreasing
  rw [gammaAfter671, at167] at decreasing
  have numeric := numeric671 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188))
  rw [oldBefore167, at167, literal, oldAfter671, gammaAfter671]
  exact numeric
theorem numeric672 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 168 p
  rw [at168] at beforeRange
  have afterRange := bonus_range 146 (HazardPattern.afterPattern 10000 p (.walk 146))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ∧ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ≤ 2 at afterRange
  rw [gammaAfter672] at afterRange
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
theorem local672 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 146) + NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) + bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 146) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 168 p at decreasing
  rw [gammaAfter672, at168] at decreasing
  have numeric := numeric672 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146))
  rw [oldBefore168, at168, literal, oldAfter672, gammaAfter672]
  exact numeric
theorem numeric673 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 168 p
  rw [at168] at beforeRange
  have afterRange := bonus_range 146 (HazardPattern.afterPattern 10000 p (.push 146 (.stay 124)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 146 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 124))) ∧ bonus (HazardPattern.nextHero (.push 146 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 124))) ≤ 2 at afterRange
  rw [gammaAfter673] at afterRange
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
theorem local673 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 146 (HazardPattern.afterPattern 10000 p (.push 146 (.stay 124))) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 146 (.stay 124)) + NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 146 (.stay 124)))) + bonus 146 (HazardPattern.afterPattern 10000 p (.push 146 (.stay 124))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 146 (.stay 124)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 146 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 124))) < bonus 168 p at decreasing
  rw [gammaAfter673, at168] at decreasing
  have numeric := numeric673 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 146 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 124)))
  rw [oldBefore168, at168, literal, oldAfter673, gammaAfter673]
  exact numeric
theorem numeric674 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 168 p
  rw [at168] at beforeRange
  have afterRange := bonus_range 190 (HazardPattern.afterPattern 10000 p (.walk 190))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ∧ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ≤ 2 at afterRange
  rw [gammaAfter674] at afterRange
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
theorem local674 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 190) + NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 190))) + bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 190) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 168 p at decreasing
  rw [gammaAfter674, at168] at decreasing
  have numeric := numeric674 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190))
  rw [oldBefore168, at168, literal, oldAfter674, gammaAfter674]
  exact numeric
theorem numeric675 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 168 p
  rw [at168] at beforeRange
  have afterRange := bonus_range 190 (HazardPattern.afterPattern 10000 p (.push 190 (.stay 212)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 190 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 212))) ∧ bonus (HazardPattern.nextHero (.push 190 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 212))) ≤ 2 at afterRange
  rw [gammaAfter675] at afterRange
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
theorem local675 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 190 (HazardPattern.afterPattern 10000 p (.push 190 (.stay 212))) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 190 (.stay 212)) + NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 190 (.stay 212)))) + bonus 190 (HazardPattern.afterPattern 10000 p (.push 190 (.stay 212))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 190 (.stay 212)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 190 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 212))) < bonus 168 p at decreasing
  rw [gammaAfter675, at168] at decreasing
  have numeric := numeric675 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 190 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 212)))
  rw [oldBefore168, at168, literal, oldAfter675, gammaAfter675]
  exact numeric
theorem numeric676 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 168 p
  rw [at168] at beforeRange
  have afterRange := bonus_range 169 (HazardPattern.afterPattern 10000 p (.walk 169))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ∧ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ≤ 2 at afterRange
  rw [gammaAfter676] at afterRange
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
theorem local676 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 169) + NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) + bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 169) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 168 p at decreasing
  rw [gammaAfter676, at168] at decreasing
  have numeric := numeric676 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169))
  rw [oldBefore168, at168, literal, oldAfter676, gammaAfter676]
  exact numeric
theorem numeric677 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 168 p
  rw [at168] at beforeRange
  have afterRange := bonus_range 169 (HazardPattern.afterPattern 10000 p (.push 169 (.stay 170)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 169 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 170))) ∧ bonus (HazardPattern.nextHero (.push 169 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 170))) ≤ 2 at afterRange
  rw [gammaAfter677] at afterRange
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
theorem local677 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 169 (HazardPattern.afterPattern 10000 p (.push 169 (.stay 170))) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 169 (.stay 170)) + NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 169 (.stay 170)))) + bonus 169 (HazardPattern.afterPattern 10000 p (.push 169 (.stay 170))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 169 (.stay 170)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 169 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 170))) < bonus 168 p at decreasing
  rw [gammaAfter677, at168] at decreasing
  have numeric := numeric677 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 169 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 170)))
  rw [oldBefore168, at168, literal, oldAfter677, gammaAfter677]
  exact numeric
theorem numeric678 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 168 p
  rw [at168] at beforeRange
  have afterRange := bonus_range 167 (HazardPattern.afterPattern 10000 p (.walk 167))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ∧ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ≤ 2 at afterRange
  rw [gammaAfter678] at afterRange
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
theorem local678 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 167) + NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) + bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 167) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 168 p at decreasing
  rw [gammaAfter678, at168] at decreasing
  have numeric := numeric678 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167))
  rw [oldBefore168, at168, literal, oldAfter678, gammaAfter678]
  exact numeric
theorem numeric679 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 168 p
  rw [at168] at beforeRange
  have afterRange := bonus_range 167 (HazardPattern.afterPattern 10000 p (.push 167 (.stay 166)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 167 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 166))) ∧ bonus (HazardPattern.nextHero (.push 167 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 166))) ≤ 2 at afterRange
  rw [gammaAfter679] at afterRange
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
theorem local679 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 167 (HazardPattern.afterPattern 10000 p (.push 167 (.stay 166))) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 167 (.stay 166)) + NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 167 (.stay 166)))) + bonus 167 (HazardPattern.afterPattern 10000 p (.push 167 (.stay 166))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 167 (.stay 166)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 167 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 166))) < bonus 168 p at decreasing
  rw [gammaAfter679, at168] at decreasing
  have numeric := numeric679 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 167 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 166)))
  rw [oldBefore168, at168, literal, oldAfter679, gammaAfter679]
  exact numeric
theorem numeric680 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 168 p
  rw [at168] at beforeRange
  have afterRange := bonus_range 147 (HazardPattern.afterPattern 10000 p (.walk 147))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ∧ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ≤ 2 at afterRange
  rw [gammaAfter680] at afterRange
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
theorem local680 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 147) + NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) + bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 147) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 168 p at decreasing
  rw [gammaAfter680, at168] at decreasing
  have numeric := numeric680 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147))
  rw [oldBefore168, at168, literal, oldAfter680, gammaAfter680]
  exact numeric
theorem numeric681 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 168 p
  rw [at168] at beforeRange
  have afterRange := bonus_range 145 (HazardPattern.afterPattern 10000 p (.walk 145))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ∧ bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) ≤ 2 at afterRange
  rw [gammaAfter681] at afterRange
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
theorem local681 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 145) + NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) + bonus 145 (HazardPattern.afterPattern 10000 p (.walk 145)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 145) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) < bonus 168 p at decreasing
  rw [gammaAfter681, at168] at decreasing
  have numeric := numeric681 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145))
  rw [oldBefore168, at168, literal, oldAfter681, gammaAfter681]
  exact numeric
theorem numeric682 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 168 p
  rw [at168] at beforeRange
  have afterRange := bonus_range 191 (HazardPattern.afterPattern 10000 p (.walk 191))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ∧ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ≤ 2 at afterRange
  rw [gammaAfter682] at afterRange
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
theorem local682 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 191) + NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 191))) + bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 191) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 168 p at decreasing
  rw [gammaAfter682, at168] at decreasing
  have numeric := numeric682 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191))
  rw [oldBefore168, at168, literal, oldAfter682, gammaAfter682]
  exact numeric
theorem numeric683 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 168 p
  rw [at168] at beforeRange
  have afterRange := bonus_range 189 (HazardPattern.afterPattern 10000 p (.walk 189))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ∧ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ≤ 2 at afterRange
  rw [gammaAfter683] at afterRange
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
theorem local683 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 189) + NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 189))) + bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 189) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 168 p at decreasing
  rw [gammaAfter683, at168] at decreasing
  have numeric := numeric683 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189))
  rw [oldBefore168, at168, literal, oldAfter683, gammaAfter683]
  exact numeric
theorem numeric684 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 169 p
  rw [at169] at beforeRange
  have afterRange := bonus_range 147 (HazardPattern.afterPattern 10000 p (.walk 147))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ∧ bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) ≤ 2 at afterRange
  rw [gammaAfter684] at afterRange
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
theorem local684 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 147) + NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) + bonus 147 (HazardPattern.afterPattern 10000 p (.walk 147)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 147) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) < bonus 169 p at decreasing
  rw [gammaAfter684, at169] at decreasing
  have numeric := numeric684 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147))
  rw [oldBefore169, at169, literal, oldAfter684, gammaAfter684]
  exact numeric
theorem numeric685 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 169 p
  rw [at169] at beforeRange
  have afterRange := bonus_range 147 (HazardPattern.afterPattern 10000 p (.push 147 (.stay 125)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 147 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 125))) ∧ bonus (HazardPattern.nextHero (.push 147 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 125))) ≤ 2 at afterRange
  rw [gammaAfter685] at afterRange
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
theorem local685 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 147 (HazardPattern.afterPattern 10000 p (.push 147 (.stay 125))) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 147 (.stay 125)) + NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 147 (.stay 125)))) + bonus 147 (HazardPattern.afterPattern 10000 p (.push 147 (.stay 125))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 147 (.stay 125)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 147 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 125))) < bonus 169 p at decreasing
  rw [gammaAfter685, at169] at decreasing
  have numeric := numeric685 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 147 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 125)))
  rw [oldBefore169, at169, literal, oldAfter685, gammaAfter685]
  exact numeric
theorem numeric686 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 169 p
  rw [at169] at beforeRange
  have afterRange := bonus_range 191 (HazardPattern.afterPattern 10000 p (.walk 191))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ∧ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ≤ 2 at afterRange
  rw [gammaAfter686] at afterRange
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
theorem local686 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 191) + NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 191))) + bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 191) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 169 p at decreasing
  rw [gammaAfter686, at169] at decreasing
  have numeric := numeric686 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191))
  rw [oldBefore169, at169, literal, oldAfter686, gammaAfter686]
  exact numeric
theorem numeric687 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 169 p
  rw [at169] at beforeRange
  have afterRange := bonus_range 191 (HazardPattern.afterPattern 10000 p (.push 191 (.stay 213)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 191 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 213))) ∧ bonus (HazardPattern.nextHero (.push 191 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 213))) ≤ 2 at afterRange
  rw [gammaAfter687] at afterRange
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
theorem local687 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 191 (HazardPattern.afterPattern 10000 p (.push 191 (.stay 213))) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 191 (.stay 213)) + NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 191 (.stay 213)))) + bonus 191 (HazardPattern.afterPattern 10000 p (.push 191 (.stay 213))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 191 (.stay 213)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 191 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 213))) < bonus 169 p at decreasing
  rw [gammaAfter687, at169] at decreasing
  have numeric := numeric687 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 191 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 213)))
  rw [oldBefore169, at169, literal, oldAfter687, gammaAfter687]
  exact numeric
theorem numeric688 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 169 p
  rw [at169] at beforeRange
  have afterRange := bonus_range 170 (HazardPattern.afterPattern 10000 p (.walk 170))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ∧ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ≤ 2 at afterRange
  rw [gammaAfter688] at afterRange
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
theorem local688 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 170) + NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 170))) + bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 170) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 169 p at decreasing
  rw [gammaAfter688, at169] at decreasing
  have numeric := numeric688 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170))
  rw [oldBefore169, at169, literal, oldAfter688, gammaAfter688]
  exact numeric
theorem numeric689 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 169 p
  rw [at169] at beforeRange
  have afterRange := bonus_range 170 (HazardPattern.afterPattern 10000 p (.push 170 (.stay 171)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 170 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 171))) ∧ bonus (HazardPattern.nextHero (.push 170 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 171))) ≤ 2 at afterRange
  rw [gammaAfter689] at afterRange
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
theorem local689 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 170 (HazardPattern.afterPattern 10000 p (.push 170 (.stay 171))) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 170 (.stay 171)) + NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 170 (.stay 171)))) + bonus 170 (HazardPattern.afterPattern 10000 p (.push 170 (.stay 171))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 170 (.stay 171)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 170 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 171))) < bonus 169 p at decreasing
  rw [gammaAfter689, at169] at decreasing
  have numeric := numeric689 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 170 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 171)))
  rw [oldBefore169, at169, literal, oldAfter689, gammaAfter689]
  exact numeric
theorem numeric690 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 169 p
  rw [at169] at beforeRange
  have afterRange := bonus_range 168 (HazardPattern.afterPattern 10000 p (.walk 168))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ∧ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ≤ 2 at afterRange
  rw [gammaAfter690] at afterRange
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
theorem local690 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 168) + NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) + bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 168) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 169 p at decreasing
  rw [gammaAfter690, at169] at decreasing
  have numeric := numeric690 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168))
  rw [oldBefore169, at169, literal, oldAfter690, gammaAfter690]
  exact numeric
theorem numeric691 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 169 p
  rw [at169] at beforeRange
  have afterRange := bonus_range 168 (HazardPattern.afterPattern 10000 p (.push 168 (.stay 167)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 168 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 167))) ∧ bonus (HazardPattern.nextHero (.push 168 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 167))) ≤ 2 at afterRange
  rw [gammaAfter691] at afterRange
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
theorem local691 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 168 (HazardPattern.afterPattern 10000 p (.push 168 (.stay 167))) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 168 (.stay 167)) + NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 168 (.stay 167)))) + bonus 168 (HazardPattern.afterPattern 10000 p (.push 168 (.stay 167))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 168 (.stay 167)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 168 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 167))) < bonus 169 p at decreasing
  rw [gammaAfter691, at169] at decreasing
  have numeric := numeric691 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 168 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 167)))
  rw [oldBefore169, at169, literal, oldAfter691, gammaAfter691]
  exact numeric
theorem numeric692 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 169 p
  rw [at169] at beforeRange
  have afterRange := bonus_range 148 (HazardPattern.afterPattern 10000 p (.walk 148))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ∧ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ≤ 2 at afterRange
  rw [gammaAfter692] at afterRange
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
theorem local692 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 148) + NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 148))) + bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 148) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 169 p at decreasing
  rw [gammaAfter692, at169] at decreasing
  have numeric := numeric692 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148))
  rw [oldBefore169, at169, literal, oldAfter692, gammaAfter692]
  exact numeric
theorem numeric693 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 169 p
  rw [at169] at beforeRange
  have afterRange := bonus_range 146 (HazardPattern.afterPattern 10000 p (.walk 146))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ∧ bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) ≤ 2 at afterRange
  rw [gammaAfter693] at afterRange
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
theorem local693 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 146) + NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) + bonus 146 (HazardPattern.afterPattern 10000 p (.walk 146)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 146) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) < bonus 169 p at decreasing
  rw [gammaAfter693, at169] at decreasing
  have numeric := numeric693 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146))
  rw [oldBefore169, at169, literal, oldAfter693, gammaAfter693]
  exact numeric
theorem numeric694 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 169 p
  rw [at169] at beforeRange
  have afterRange := bonus_range 192 (HazardPattern.afterPattern 10000 p (.walk 192))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ∧ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ≤ 2 at afterRange
  rw [gammaAfter694] at afterRange
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
theorem local694 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 192) + NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 192))) + bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 192) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 169 p at decreasing
  rw [gammaAfter694, at169] at decreasing
  have numeric := numeric694 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192))
  rw [oldBefore169, at169, literal, oldAfter694, gammaAfter694]
  exact numeric
theorem numeric695 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 169 p
  rw [at169] at beforeRange
  have afterRange := bonus_range 190 (HazardPattern.afterPattern 10000 p (.walk 190))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ∧ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ≤ 2 at afterRange
  rw [gammaAfter695] at afterRange
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
theorem local695 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 190) + NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 190))) + bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 190) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 169 p at decreasing
  rw [gammaAfter695, at169] at decreasing
  have numeric := numeric695 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190))
  rw [oldBefore169, at169, literal, oldAfter695, gammaAfter695]
  exact numeric
theorem numeric696 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 170 p
  rw [at170] at beforeRange
  have afterRange := bonus_range 148 (HazardPattern.afterPattern 10000 p (.walk 148))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ∧ bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) ≤ 2 at afterRange
  rw [gammaAfter696] at afterRange
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
theorem local696 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 148) + NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 148))) + bonus 148 (HazardPattern.afterPattern 10000 p (.walk 148)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 148) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) < bonus 170 p at decreasing
  rw [gammaAfter696, at170] at decreasing
  have numeric := numeric696 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148))
  rw [oldBefore170, at170, literal, oldAfter696, gammaAfter696]
  exact numeric
theorem numeric697 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 170 p
  rw [at170] at beforeRange
  have afterRange := bonus_range 148 (HazardPattern.afterPattern 10000 p (.push 148 (.stay 126)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 148 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 126))) ∧ bonus (HazardPattern.nextHero (.push 148 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 126))) ≤ 2 at afterRange
  rw [gammaAfter697] at afterRange
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
theorem local697 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 148 (HazardPattern.afterPattern 10000 p (.push 148 (.stay 126))) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 148 (.stay 126)) + NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 148 (.stay 126)))) + bonus 148 (HazardPattern.afterPattern 10000 p (.push 148 (.stay 126))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 148 (.stay 126)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 148 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 126))) < bonus 170 p at decreasing
  rw [gammaAfter697, at170] at decreasing
  have numeric := numeric697 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 148 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 126)))
  rw [oldBefore170, at170, literal, oldAfter697, gammaAfter697]
  exact numeric
theorem numeric698 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 170 p
  rw [at170] at beforeRange
  have afterRange := bonus_range 192 (HazardPattern.afterPattern 10000 p (.walk 192))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ∧ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ≤ 2 at afterRange
  rw [gammaAfter698] at afterRange
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
theorem local698 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 192) + NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 192))) + bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 192) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 170 p at decreasing
  rw [gammaAfter698, at170] at decreasing
  have numeric := numeric698 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192))
  rw [oldBefore170, at170, literal, oldAfter698, gammaAfter698]
  exact numeric
theorem numeric699 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 170 p
  rw [at170] at beforeRange
  have afterRange := bonus_range 192 (HazardPattern.afterPattern 10000 p (.push 192 (.stay 214)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 192 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 214))) ∧ bonus (HazardPattern.nextHero (.push 192 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 214))) ≤ 2 at afterRange
  rw [gammaAfter699] at afterRange
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
theorem local699 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 192 (HazardPattern.afterPattern 10000 p (.push 192 (.stay 214))) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 192 (.stay 214)) + NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 192 (.stay 214)))) + bonus 192 (HazardPattern.afterPattern 10000 p (.push 192 (.stay 214))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 192 (.stay 214)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 192 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 214))) < bonus 170 p at decreasing
  rw [gammaAfter699, at170] at decreasing
  have numeric := numeric699 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 192 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 214)))
  rw [oldBefore170, at170, literal, oldAfter699, gammaAfter699]
  exact numeric
end NetHack.Soko22Hazard87
