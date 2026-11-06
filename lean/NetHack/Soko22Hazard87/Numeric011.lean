import NetHack.Soko22Hazard87.Numeric010
import NetHack.Soko22Hazard87.AndIntroBlocks0223
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric770 (p : Pattern) (guard : d192712 p = 1) (decreasing : d20389 p < d20891 p) :
    d49102 p + d20891 p ≤ (0 : Int) + d48997 p + d20389 p := by
  have beforeRange := bonus_range 186 p
  rw [at186] at beforeRange
  have afterRange := bonus_range 163 (HazardPattern.afterPattern 10000 p (.walk 163))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) ∧ bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) ≤ 2 at afterRange
  rw [gammaAfter770] at afterRange
  have possibilities : (d20891 p = 1 ∧ d20389 p = 0) ∨ (d20891 p = 2 ∧ d20389 p = 0) ∨ (d20891 p = 2 ∧ d20389 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro11000 p pair.1
    have afterEq := eqIntro10791 p pair.2
    have combined := andIntro55993 p beforeEq guard
    have complete := andIntro45158 p afterEq combined
    have bound := compare28852 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10791 p pair.2
    have combined := andIntro55998 p guard beforeEq
    have complete := andIntro45225 p afterEq combined
    have bound := compare28853 p complete
    omega
  · have beforeEq := eqIntro17889 p pair.1
    have afterEq := eqIntro10843 p pair.2
    have combined := andIntro55998 p guard beforeEq
    have complete := andIntro45253 p afterEq combined
    have bound := compare28852 p complete
    omega
theorem local770 (p : Pattern) (guard : d192712 p = 1)
    (decreasing : bonus 163 (HazardPattern.afterPattern 10000 p (.walk 163)) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 163) + NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 163))) + bonus 163 (HazardPattern.afterPattern 10000 p (.walk 163)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 163) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) < bonus 186 p at decreasing
  rw [gammaAfter770, at186] at decreasing
  have numeric := numeric770 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163))
  rw [oldBefore186, at186, literal, oldAfter770, gammaAfter770]
  exact numeric
theorem numeric771 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 188 p
  rw [at188] at beforeRange
  have afterRange := bonus_range 166 (HazardPattern.afterPattern 10000 p (.walk 166))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) ∧ bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) ≤ 2 at afterRange
  rw [gammaAfter771] at afterRange
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
theorem local771 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 166 (HazardPattern.afterPattern 10000 p (.walk 166)) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 166) + NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 166))) + bonus 166 (HazardPattern.afterPattern 10000 p (.walk 166)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 166) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) < bonus 188 p at decreasing
  rw [gammaAfter771, at188] at decreasing
  have numeric := numeric771 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166))
  rw [oldBefore188, at188, literal, oldAfter771, gammaAfter771]
  exact numeric
theorem numeric772 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 188 p
  rw [at188] at beforeRange
  have afterRange := bonus_range 166 (HazardPattern.afterPattern 10000 p (.push 166 (.stay 144)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 166 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 166 (.stay 144))) ∧ bonus (HazardPattern.nextHero (.push 166 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 166 (.stay 144))) ≤ 2 at afterRange
  rw [gammaAfter772] at afterRange
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
theorem local772 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 166 (HazardPattern.afterPattern 10000 p (.push 166 (.stay 144))) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 166 (.stay 144)) + NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 166 (.stay 144)))) + bonus 166 (HazardPattern.afterPattern 10000 p (.push 166 (.stay 144))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 166 (.stay 144)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 166 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 166 (.stay 144))) < bonus 188 p at decreasing
  rw [gammaAfter772, at188] at decreasing
  have numeric := numeric772 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 166 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 166 (.stay 144)))
  rw [oldBefore188, at188, literal, oldAfter772, gammaAfter772]
  exact numeric
theorem numeric773 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 188 p
  rw [at188] at beforeRange
  have afterRange := bonus_range 210 (HazardPattern.afterPattern 10000 p (.walk 210))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210)) ∧ bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210)) ≤ 2 at afterRange
  rw [gammaAfter773] at afterRange
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
theorem local773 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 210 (HazardPattern.afterPattern 10000 p (.walk 210)) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 210) + NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 210))) + bonus 210 (HazardPattern.afterPattern 10000 p (.walk 210)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 210) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210)) < bonus 188 p at decreasing
  rw [gammaAfter773, at188] at decreasing
  have numeric := numeric773 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210))
  rw [oldBefore188, at188, literal, oldAfter773, gammaAfter773]
  exact numeric
theorem numeric774 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 188 p
  rw [at188] at beforeRange
  have afterRange := bonus_range 189 (HazardPattern.afterPattern 10000 p (.walk 189))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ∧ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ≤ 2 at afterRange
  rw [gammaAfter774] at afterRange
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
theorem local774 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 189) + NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 189))) + bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 189) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 188 p at decreasing
  rw [gammaAfter774, at188] at decreasing
  have numeric := numeric774 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189))
  rw [oldBefore188, at188, literal, oldAfter774, gammaAfter774]
  exact numeric
theorem numeric775 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 188 p
  rw [at188] at beforeRange
  have afterRange := bonus_range 189 (HazardPattern.afterPattern 10000 p (.push 189 (.stay 190)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 189 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 190))) ∧ bonus (HazardPattern.nextHero (.push 189 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 190))) ≤ 2 at afterRange
  rw [gammaAfter775] at afterRange
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
theorem local775 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 189 (HazardPattern.afterPattern 10000 p (.push 189 (.stay 190))) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 189 (.stay 190)) + NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 189 (.stay 190)))) + bonus 189 (HazardPattern.afterPattern 10000 p (.push 189 (.stay 190))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 189 (.stay 190)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 189 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 190))) < bonus 188 p at decreasing
  rw [gammaAfter775, at188] at decreasing
  have numeric := numeric775 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 189 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 190)))
  rw [oldBefore188, at188, literal, oldAfter775, gammaAfter775]
  exact numeric
theorem numeric776 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 188 p
  rw [at188] at beforeRange
  have afterRange := bonus_range 167 (HazardPattern.afterPattern 10000 p (.walk 167))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ∧ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ≤ 2 at afterRange
  rw [gammaAfter776] at afterRange
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
theorem local776 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 167) + NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) + bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 167) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 188 p at decreasing
  rw [gammaAfter776, at188] at decreasing
  have numeric := numeric776 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167))
  rw [oldBefore188, at188, literal, oldAfter776, gammaAfter776]
  exact numeric
theorem numeric777 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 188 p
  rw [at188] at beforeRange
  have afterRange := bonus_range 211 (HazardPattern.afterPattern 10000 p (.walk 211))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) ∧ bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) ≤ 2 at afterRange
  rw [gammaAfter777] at afterRange
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
theorem local777 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 211 (HazardPattern.afterPattern 10000 p (.walk 211)) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 211) + NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 211))) + bonus 211 (HazardPattern.afterPattern 10000 p (.walk 211)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 211) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) < bonus 188 p at decreasing
  rw [gammaAfter777, at188] at decreasing
  have numeric := numeric777 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211))
  rw [oldBefore188, at188, literal, oldAfter777, gammaAfter777]
  exact numeric
theorem numeric778 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 189 p
  rw [at189] at beforeRange
  have afterRange := bonus_range 167 (HazardPattern.afterPattern 10000 p (.walk 167))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ∧ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ≤ 2 at afterRange
  rw [gammaAfter778] at afterRange
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
theorem local778 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 167) + NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) + bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 167) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 189 p at decreasing
  rw [gammaAfter778, at189] at decreasing
  have numeric := numeric778 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167))
  rw [oldBefore189, at189, literal, oldAfter778, gammaAfter778]
  exact numeric
theorem numeric779 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 189 p
  rw [at189] at beforeRange
  have afterRange := bonus_range 167 (HazardPattern.afterPattern 10000 p (.push 167 (.stay 145)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 167 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 145))) ∧ bonus (HazardPattern.nextHero (.push 167 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 145))) ≤ 2 at afterRange
  rw [gammaAfter779] at afterRange
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
theorem local779 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 167 (HazardPattern.afterPattern 10000 p (.push 167 (.stay 145))) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 167 (.stay 145)) + NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 167 (.stay 145)))) + bonus 167 (HazardPattern.afterPattern 10000 p (.push 167 (.stay 145))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 167 (.stay 145)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 167 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 145))) < bonus 189 p at decreasing
  rw [gammaAfter779, at189] at decreasing
  have numeric := numeric779 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 167 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 145)))
  rw [oldBefore189, at189, literal, oldAfter779, gammaAfter779]
  exact numeric
theorem numeric780 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 189 p
  rw [at189] at beforeRange
  have afterRange := bonus_range 211 (HazardPattern.afterPattern 10000 p (.walk 211))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) ∧ bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) ≤ 2 at afterRange
  rw [gammaAfter780] at afterRange
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
theorem local780 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 211 (HazardPattern.afterPattern 10000 p (.walk 211)) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 211) + NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 211))) + bonus 211 (HazardPattern.afterPattern 10000 p (.walk 211)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 211) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) < bonus 189 p at decreasing
  rw [gammaAfter780, at189] at decreasing
  have numeric := numeric780 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211))
  rw [oldBefore189, at189, literal, oldAfter780, gammaAfter780]
  exact numeric
theorem numeric781 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 189 p
  rw [at189] at beforeRange
  have afterRange := bonus_range 190 (HazardPattern.afterPattern 10000 p (.walk 190))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ∧ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ≤ 2 at afterRange
  rw [gammaAfter781] at afterRange
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
theorem local781 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 190) + NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 190))) + bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 190) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 189 p at decreasing
  rw [gammaAfter781, at189] at decreasing
  have numeric := numeric781 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190))
  rw [oldBefore189, at189, literal, oldAfter781, gammaAfter781]
  exact numeric
theorem numeric782 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 189 p
  rw [at189] at beforeRange
  have afterRange := bonus_range 190 (HazardPattern.afterPattern 10000 p (.push 190 (.stay 191)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 190 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 191))) ∧ bonus (HazardPattern.nextHero (.push 190 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 191))) ≤ 2 at afterRange
  rw [gammaAfter782] at afterRange
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
theorem local782 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 190 (HazardPattern.afterPattern 10000 p (.push 190 (.stay 191))) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 190 (.stay 191)) + NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 190 (.stay 191)))) + bonus 190 (HazardPattern.afterPattern 10000 p (.push 190 (.stay 191))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 190 (.stay 191)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 190 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 191))) < bonus 189 p at decreasing
  rw [gammaAfter782, at189] at decreasing
  have numeric := numeric782 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 190 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 191)))
  rw [oldBefore189, at189, literal, oldAfter782, gammaAfter782]
  exact numeric
theorem numeric783 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 189 p
  rw [at189] at beforeRange
  have afterRange := bonus_range 188 (HazardPattern.afterPattern 10000 p (.walk 188))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) ∧ bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) ≤ 2 at afterRange
  rw [gammaAfter783] at afterRange
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
theorem local783 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 188 (HazardPattern.afterPattern 10000 p (.walk 188)) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 188) + NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 188))) + bonus 188 (HazardPattern.afterPattern 10000 p (.walk 188)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 188) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) < bonus 189 p at decreasing
  rw [gammaAfter783, at189] at decreasing
  have numeric := numeric783 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188))
  rw [oldBefore189, at189, literal, oldAfter783, gammaAfter783]
  exact numeric
theorem numeric784 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 189 p
  rw [at189] at beforeRange
  have afterRange := bonus_range 168 (HazardPattern.afterPattern 10000 p (.walk 168))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ∧ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ≤ 2 at afterRange
  rw [gammaAfter784] at afterRange
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
theorem local784 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 168) + NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) + bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 168) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 189 p at decreasing
  rw [gammaAfter784, at189] at decreasing
  have numeric := numeric784 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168))
  rw [oldBefore189, at189, literal, oldAfter784, gammaAfter784]
  exact numeric
theorem numeric785 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 189 p
  rw [at189] at beforeRange
  have afterRange := bonus_range 166 (HazardPattern.afterPattern 10000 p (.walk 166))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) ∧ bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) ≤ 2 at afterRange
  rw [gammaAfter785] at afterRange
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
theorem local785 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 166 (HazardPattern.afterPattern 10000 p (.walk 166)) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 166) + NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 166))) + bonus 166 (HazardPattern.afterPattern 10000 p (.walk 166)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 166) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) < bonus 189 p at decreasing
  rw [gammaAfter785, at189] at decreasing
  have numeric := numeric785 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166))
  rw [oldBefore189, at189, literal, oldAfter785, gammaAfter785]
  exact numeric
theorem numeric786 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 189 p
  rw [at189] at beforeRange
  have afterRange := bonus_range 212 (HazardPattern.afterPattern 10000 p (.walk 212))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) ∧ bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) ≤ 2 at afterRange
  rw [gammaAfter786] at afterRange
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
theorem local786 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 212 (HazardPattern.afterPattern 10000 p (.walk 212)) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 212) + NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 212))) + bonus 212 (HazardPattern.afterPattern 10000 p (.walk 212)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 212) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) < bonus 189 p at decreasing
  rw [gammaAfter786, at189] at decreasing
  have numeric := numeric786 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212))
  rw [oldBefore189, at189, literal, oldAfter786, gammaAfter786]
  exact numeric
theorem numeric787 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 189 p
  rw [at189] at beforeRange
  have afterRange := bonus_range 210 (HazardPattern.afterPattern 10000 p (.walk 210))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210)) ∧ bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210)) ≤ 2 at afterRange
  rw [gammaAfter787] at afterRange
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
theorem local787 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 210 (HazardPattern.afterPattern 10000 p (.walk 210)) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 210) + NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 210))) + bonus 210 (HazardPattern.afterPattern 10000 p (.walk 210)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 210) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210)) < bonus 189 p at decreasing
  rw [gammaAfter787, at189] at decreasing
  have numeric := numeric787 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210))
  rw [oldBefore189, at189, literal, oldAfter787, gammaAfter787]
  exact numeric
theorem numeric788 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 190 p
  rw [at190] at beforeRange
  have afterRange := bonus_range 168 (HazardPattern.afterPattern 10000 p (.walk 168))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ∧ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ≤ 2 at afterRange
  rw [gammaAfter788] at afterRange
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
theorem local788 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 168) + NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) + bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 168) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 190 p at decreasing
  rw [gammaAfter788, at190] at decreasing
  have numeric := numeric788 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168))
  rw [oldBefore190, at190, literal, oldAfter788, gammaAfter788]
  exact numeric
theorem numeric789 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 190 p
  rw [at190] at beforeRange
  have afterRange := bonus_range 168 (HazardPattern.afterPattern 10000 p (.push 168 (.stay 146)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 168 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 146))) ∧ bonus (HazardPattern.nextHero (.push 168 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 146))) ≤ 2 at afterRange
  rw [gammaAfter789] at afterRange
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
theorem local789 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 168 (HazardPattern.afterPattern 10000 p (.push 168 (.stay 146))) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 168 (.stay 146)) + NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 168 (.stay 146)))) + bonus 168 (HazardPattern.afterPattern 10000 p (.push 168 (.stay 146))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 168 (.stay 146)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 168 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 146))) < bonus 190 p at decreasing
  rw [gammaAfter789, at190] at decreasing
  have numeric := numeric789 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 168 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 146)))
  rw [oldBefore190, at190, literal, oldAfter789, gammaAfter789]
  exact numeric
theorem numeric790 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 190 p
  rw [at190] at beforeRange
  have afterRange := bonus_range 212 (HazardPattern.afterPattern 10000 p (.walk 212))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) ∧ bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) ≤ 2 at afterRange
  rw [gammaAfter790] at afterRange
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
theorem local790 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 212 (HazardPattern.afterPattern 10000 p (.walk 212)) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 212) + NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 212))) + bonus 212 (HazardPattern.afterPattern 10000 p (.walk 212)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 212) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) < bonus 190 p at decreasing
  rw [gammaAfter790, at190] at decreasing
  have numeric := numeric790 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212))
  rw [oldBefore190, at190, literal, oldAfter790, gammaAfter790]
  exact numeric
theorem numeric791 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 190 p
  rw [at190] at beforeRange
  have afterRange := bonus_range 191 (HazardPattern.afterPattern 10000 p (.walk 191))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ∧ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ≤ 2 at afterRange
  rw [gammaAfter791] at afterRange
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
theorem local791 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 191) + NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 191))) + bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 191) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 190 p at decreasing
  rw [gammaAfter791, at190] at decreasing
  have numeric := numeric791 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191))
  rw [oldBefore190, at190, literal, oldAfter791, gammaAfter791]
  exact numeric
theorem numeric792 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 190 p
  rw [at190] at beforeRange
  have afterRange := bonus_range 191 (HazardPattern.afterPattern 10000 p (.push 191 (.stay 192)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 191 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 192))) ∧ bonus (HazardPattern.nextHero (.push 191 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 192))) ≤ 2 at afterRange
  rw [gammaAfter792] at afterRange
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
theorem local792 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 191 (HazardPattern.afterPattern 10000 p (.push 191 (.stay 192))) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 191 (.stay 192)) + NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 191 (.stay 192)))) + bonus 191 (HazardPattern.afterPattern 10000 p (.push 191 (.stay 192))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 191 (.stay 192)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 191 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 192))) < bonus 190 p at decreasing
  rw [gammaAfter792, at190] at decreasing
  have numeric := numeric792 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 191 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 192)))
  rw [oldBefore190, at190, literal, oldAfter792, gammaAfter792]
  exact numeric
theorem numeric793 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 190 p
  rw [at190] at beforeRange
  have afterRange := bonus_range 189 (HazardPattern.afterPattern 10000 p (.walk 189))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ∧ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ≤ 2 at afterRange
  rw [gammaAfter793] at afterRange
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
theorem local793 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 189) + NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 189))) + bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 189) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 190 p at decreasing
  rw [gammaAfter793, at190] at decreasing
  have numeric := numeric793 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189))
  rw [oldBefore190, at190, literal, oldAfter793, gammaAfter793]
  exact numeric
theorem numeric794 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 190 p
  rw [at190] at beforeRange
  have afterRange := bonus_range 189 (HazardPattern.afterPattern 10000 p (.push 189 (.stay 188)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 189 (.stay 188))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 188))) ∧ bonus (HazardPattern.nextHero (.push 189 (.stay 188))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 188))) ≤ 2 at afterRange
  rw [gammaAfter794] at afterRange
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
theorem local794 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 189 (HazardPattern.afterPattern 10000 p (.push 189 (.stay 188))) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 189 (.stay 188)) + NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 189 (.stay 188)))) + bonus 189 (HazardPattern.afterPattern 10000 p (.push 189 (.stay 188))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 189 (.stay 188)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 189 (.stay 188))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 188))) < bonus 190 p at decreasing
  rw [gammaAfter794, at190] at decreasing
  have numeric := numeric794 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 189 (.stay 188))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 188)))
  rw [oldBefore190, at190, literal, oldAfter794, gammaAfter794]
  exact numeric
theorem numeric795 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 190 p
  rw [at190] at beforeRange
  have afterRange := bonus_range 169 (HazardPattern.afterPattern 10000 p (.walk 169))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ∧ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ≤ 2 at afterRange
  rw [gammaAfter795] at afterRange
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
theorem local795 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 169) + NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) + bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 169) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 190 p at decreasing
  rw [gammaAfter795, at190] at decreasing
  have numeric := numeric795 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169))
  rw [oldBefore190, at190, literal, oldAfter795, gammaAfter795]
  exact numeric
theorem numeric796 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 190 p
  rw [at190] at beforeRange
  have afterRange := bonus_range 167 (HazardPattern.afterPattern 10000 p (.walk 167))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ∧ bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) ≤ 2 at afterRange
  rw [gammaAfter796] at afterRange
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
theorem local796 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 167) + NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) + bonus 167 (HazardPattern.afterPattern 10000 p (.walk 167)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 167) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) < bonus 190 p at decreasing
  rw [gammaAfter796, at190] at decreasing
  have numeric := numeric796 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167))
  rw [oldBefore190, at190, literal, oldAfter796, gammaAfter796]
  exact numeric
theorem numeric797 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 190 p
  rw [at190] at beforeRange
  have afterRange := bonus_range 213 (HazardPattern.afterPattern 10000 p (.walk 213))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) ∧ bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) ≤ 2 at afterRange
  rw [gammaAfter797] at afterRange
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
theorem local797 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 213 (HazardPattern.afterPattern 10000 p (.walk 213)) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 213) + NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 213))) + bonus 213 (HazardPattern.afterPattern 10000 p (.walk 213)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 213) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) < bonus 190 p at decreasing
  rw [gammaAfter797, at190] at decreasing
  have numeric := numeric797 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213))
  rw [oldBefore190, at190, literal, oldAfter797, gammaAfter797]
  exact numeric
theorem numeric798 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 190 p
  rw [at190] at beforeRange
  have afterRange := bonus_range 211 (HazardPattern.afterPattern 10000 p (.walk 211))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) ∧ bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) ≤ 2 at afterRange
  rw [gammaAfter798] at afterRange
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
theorem local798 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 211 (HazardPattern.afterPattern 10000 p (.walk 211)) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 211) + NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 211))) + bonus 211 (HazardPattern.afterPattern 10000 p (.walk 211)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 211) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) < bonus 190 p at decreasing
  rw [gammaAfter798, at190] at decreasing
  have numeric := numeric798 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211))
  rw [oldBefore190, at190, literal, oldAfter798, gammaAfter798]
  exact numeric
theorem numeric799 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 191 p
  rw [at191] at beforeRange
  have afterRange := bonus_range 169 (HazardPattern.afterPattern 10000 p (.walk 169))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ∧ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ≤ 2 at afterRange
  rw [gammaAfter799] at afterRange
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
theorem local799 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 169) + NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) + bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 169) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 191 p at decreasing
  rw [gammaAfter799, at191] at decreasing
  have numeric := numeric799 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169))
  rw [oldBefore191, at191, literal, oldAfter799, gammaAfter799]
  exact numeric
theorem numeric800 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 191 p
  rw [at191] at beforeRange
  have afterRange := bonus_range 169 (HazardPattern.afterPattern 10000 p (.push 169 (.stay 147)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 169 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 147))) ∧ bonus (HazardPattern.nextHero (.push 169 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 147))) ≤ 2 at afterRange
  rw [gammaAfter800] at afterRange
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
theorem local800 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 169 (HazardPattern.afterPattern 10000 p (.push 169 (.stay 147))) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 169 (.stay 147)) + NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 169 (.stay 147)))) + bonus 169 (HazardPattern.afterPattern 10000 p (.push 169 (.stay 147))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 169 (.stay 147)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 169 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 147))) < bonus 191 p at decreasing
  rw [gammaAfter800, at191] at decreasing
  have numeric := numeric800 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 169 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 147)))
  rw [oldBefore191, at191, literal, oldAfter800, gammaAfter800]
  exact numeric
theorem numeric801 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 191 p
  rw [at191] at beforeRange
  have afterRange := bonus_range 213 (HazardPattern.afterPattern 10000 p (.walk 213))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) ∧ bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) ≤ 2 at afterRange
  rw [gammaAfter801] at afterRange
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
theorem local801 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 213 (HazardPattern.afterPattern 10000 p (.walk 213)) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 213) + NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 213))) + bonus 213 (HazardPattern.afterPattern 10000 p (.walk 213)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 213) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) < bonus 191 p at decreasing
  rw [gammaAfter801, at191] at decreasing
  have numeric := numeric801 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213))
  rw [oldBefore191, at191, literal, oldAfter801, gammaAfter801]
  exact numeric
theorem numeric802 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 191 p
  rw [at191] at beforeRange
  have afterRange := bonus_range 192 (HazardPattern.afterPattern 10000 p (.walk 192))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ∧ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ≤ 2 at afterRange
  rw [gammaAfter802] at afterRange
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
theorem local802 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 192) + NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 192))) + bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 192) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 191 p at decreasing
  rw [gammaAfter802, at191] at decreasing
  have numeric := numeric802 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192))
  rw [oldBefore191, at191, literal, oldAfter802, gammaAfter802]
  exact numeric
theorem numeric803 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 191 p
  rw [at191] at beforeRange
  have afterRange := bonus_range 192 (HazardPattern.afterPattern 10000 p (.push 192 (.stay 193)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 192 (.stay 193))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 193))) ∧ bonus (HazardPattern.nextHero (.push 192 (.stay 193))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 193))) ≤ 2 at afterRange
  rw [gammaAfter803] at afterRange
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
theorem local803 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 192 (HazardPattern.afterPattern 10000 p (.push 192 (.stay 193))) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 192 (.stay 193)) + NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 192 (.stay 193)))) + bonus 192 (HazardPattern.afterPattern 10000 p (.push 192 (.stay 193))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 192 (.stay 193)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 192 (.stay 193))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 193))) < bonus 191 p at decreasing
  rw [gammaAfter803, at191] at decreasing
  have numeric := numeric803 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 192 (.stay 193))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 193)))
  rw [oldBefore191, at191, literal, oldAfter803, gammaAfter803]
  exact numeric
theorem numeric804 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 191 p
  rw [at191] at beforeRange
  have afterRange := bonus_range 190 (HazardPattern.afterPattern 10000 p (.walk 190))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ∧ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ≤ 2 at afterRange
  rw [gammaAfter804] at afterRange
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
theorem local804 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 190) + NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 190))) + bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 190) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 191 p at decreasing
  rw [gammaAfter804, at191] at decreasing
  have numeric := numeric804 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190))
  rw [oldBefore191, at191, literal, oldAfter804, gammaAfter804]
  exact numeric
theorem numeric805 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 191 p
  rw [at191] at beforeRange
  have afterRange := bonus_range 190 (HazardPattern.afterPattern 10000 p (.push 190 (.stay 189)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 190 (.stay 189))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 189))) ∧ bonus (HazardPattern.nextHero (.push 190 (.stay 189))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 189))) ≤ 2 at afterRange
  rw [gammaAfter805] at afterRange
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
theorem local805 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 190 (HazardPattern.afterPattern 10000 p (.push 190 (.stay 189))) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 190 (.stay 189)) + NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 190 (.stay 189)))) + bonus 190 (HazardPattern.afterPattern 10000 p (.push 190 (.stay 189))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 190 (.stay 189)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 190 (.stay 189))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 189))) < bonus 191 p at decreasing
  rw [gammaAfter805, at191] at decreasing
  have numeric := numeric805 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 190 (.stay 189))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 189)))
  rw [oldBefore191, at191, literal, oldAfter805, gammaAfter805]
  exact numeric
theorem numeric806 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 191 p
  rw [at191] at beforeRange
  have afterRange := bonus_range 170 (HazardPattern.afterPattern 10000 p (.walk 170))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ∧ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ≤ 2 at afterRange
  rw [gammaAfter806] at afterRange
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
theorem local806 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 170) + NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 170))) + bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 170) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 191 p at decreasing
  rw [gammaAfter806, at191] at decreasing
  have numeric := numeric806 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170))
  rw [oldBefore191, at191, literal, oldAfter806, gammaAfter806]
  exact numeric
theorem numeric807 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 191 p
  rw [at191] at beforeRange
  have afterRange := bonus_range 168 (HazardPattern.afterPattern 10000 p (.walk 168))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ∧ bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) ≤ 2 at afterRange
  rw [gammaAfter807] at afterRange
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
theorem local807 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 168) + NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) + bonus 168 (HazardPattern.afterPattern 10000 p (.walk 168)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 168) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) < bonus 191 p at decreasing
  rw [gammaAfter807, at191] at decreasing
  have numeric := numeric807 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168))
  rw [oldBefore191, at191, literal, oldAfter807, gammaAfter807]
  exact numeric
theorem numeric808 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 191 p
  rw [at191] at beforeRange
  have afterRange := bonus_range 214 (HazardPattern.afterPattern 10000 p (.walk 214))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) ∧ bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) ≤ 2 at afterRange
  rw [gammaAfter808] at afterRange
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
theorem local808 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 214 (HazardPattern.afterPattern 10000 p (.walk 214)) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 214) + NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 214))) + bonus 214 (HazardPattern.afterPattern 10000 p (.walk 214)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 214) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) < bonus 191 p at decreasing
  rw [gammaAfter808, at191] at decreasing
  have numeric := numeric808 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214))
  rw [oldBefore191, at191, literal, oldAfter808, gammaAfter808]
  exact numeric
theorem numeric809 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 191 p
  rw [at191] at beforeRange
  have afterRange := bonus_range 212 (HazardPattern.afterPattern 10000 p (.walk 212))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) ∧ bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) ≤ 2 at afterRange
  rw [gammaAfter809] at afterRange
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
theorem local809 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 212 (HazardPattern.afterPattern 10000 p (.walk 212)) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 212) + NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 212))) + bonus 212 (HazardPattern.afterPattern 10000 p (.walk 212)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 212) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) < bonus 191 p at decreasing
  rw [gammaAfter809, at191] at decreasing
  have numeric := numeric809 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212))
  rw [oldBefore191, at191, literal, oldAfter809, gammaAfter809]
  exact numeric
theorem numeric810 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 192 p
  rw [at192] at beforeRange
  have afterRange := bonus_range 170 (HazardPattern.afterPattern 10000 p (.walk 170))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ∧ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ≤ 2 at afterRange
  rw [gammaAfter810] at afterRange
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
theorem local810 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 170) + NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 170))) + bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 170) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 192 p at decreasing
  rw [gammaAfter810, at192] at decreasing
  have numeric := numeric810 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170))
  rw [oldBefore192, at192, literal, oldAfter810, gammaAfter810]
  exact numeric
theorem numeric811 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 192 p
  rw [at192] at beforeRange
  have afterRange := bonus_range 170 (HazardPattern.afterPattern 10000 p (.push 170 (.stay 148)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 170 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 148))) ∧ bonus (HazardPattern.nextHero (.push 170 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 148))) ≤ 2 at afterRange
  rw [gammaAfter811] at afterRange
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
theorem local811 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 170 (HazardPattern.afterPattern 10000 p (.push 170 (.stay 148))) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 170 (.stay 148)) + NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 170 (.stay 148)))) + bonus 170 (HazardPattern.afterPattern 10000 p (.push 170 (.stay 148))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 170 (.stay 148)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 170 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 148))) < bonus 192 p at decreasing
  rw [gammaAfter811, at192] at decreasing
  have numeric := numeric811 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 170 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 148)))
  rw [oldBefore192, at192, literal, oldAfter811, gammaAfter811]
  exact numeric
theorem numeric812 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 192 p
  rw [at192] at beforeRange
  have afterRange := bonus_range 214 (HazardPattern.afterPattern 10000 p (.walk 214))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) ∧ bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) ≤ 2 at afterRange
  rw [gammaAfter812] at afterRange
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
theorem local812 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 214 (HazardPattern.afterPattern 10000 p (.walk 214)) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 214) + NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 214))) + bonus 214 (HazardPattern.afterPattern 10000 p (.walk 214)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 214) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) < bonus 192 p at decreasing
  rw [gammaAfter812, at192] at decreasing
  have numeric := numeric812 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214))
  rw [oldBefore192, at192, literal, oldAfter812, gammaAfter812]
  exact numeric
theorem numeric813 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 192 p
  rw [at192] at beforeRange
  have afterRange := bonus_range 193 (HazardPattern.afterPattern 10000 p (.walk 193))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ∧ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ≤ 2 at afterRange
  rw [gammaAfter813] at afterRange
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
theorem local813 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 193) + NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 193))) + bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 193) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 192 p at decreasing
  rw [gammaAfter813, at192] at decreasing
  have numeric := numeric813 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193))
  rw [oldBefore192, at192, literal, oldAfter813, gammaAfter813]
  exact numeric
theorem numeric814 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 192 p
  rw [at192] at beforeRange
  have afterRange := bonus_range 193 (HazardPattern.afterPattern 10000 p (.push 193 (.stay 194)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 193 (.stay 194))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 194))) ∧ bonus (HazardPattern.nextHero (.push 193 (.stay 194))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 194))) ≤ 2 at afterRange
  rw [gammaAfter814] at afterRange
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
theorem local814 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 193 (HazardPattern.afterPattern 10000 p (.push 193 (.stay 194))) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 193 (.stay 194)) + NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 193 (.stay 194)))) + bonus 193 (HazardPattern.afterPattern 10000 p (.push 193 (.stay 194))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 193 (.stay 194)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 193 (.stay 194))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 194))) < bonus 192 p at decreasing
  rw [gammaAfter814, at192] at decreasing
  have numeric := numeric814 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 193 (.stay 194))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 194)))
  rw [oldBefore192, at192, literal, oldAfter814, gammaAfter814]
  exact numeric
theorem numeric815 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 192 p
  rw [at192] at beforeRange
  have afterRange := bonus_range 191 (HazardPattern.afterPattern 10000 p (.walk 191))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ∧ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ≤ 2 at afterRange
  rw [gammaAfter815] at afterRange
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
theorem local815 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 191) + NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 191))) + bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 191) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 192 p at decreasing
  rw [gammaAfter815, at192] at decreasing
  have numeric := numeric815 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191))
  rw [oldBefore192, at192, literal, oldAfter815, gammaAfter815]
  exact numeric
theorem numeric816 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 192 p
  rw [at192] at beforeRange
  have afterRange := bonus_range 191 (HazardPattern.afterPattern 10000 p (.push 191 (.stay 190)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 191 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 190))) ∧ bonus (HazardPattern.nextHero (.push 191 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 190))) ≤ 2 at afterRange
  rw [gammaAfter816] at afterRange
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
theorem local816 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 191 (HazardPattern.afterPattern 10000 p (.push 191 (.stay 190))) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 191 (.stay 190)) + NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 191 (.stay 190)))) + bonus 191 (HazardPattern.afterPattern 10000 p (.push 191 (.stay 190))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 191 (.stay 190)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 191 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 190))) < bonus 192 p at decreasing
  rw [gammaAfter816, at192] at decreasing
  have numeric := numeric816 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 191 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 190)))
  rw [oldBefore192, at192, literal, oldAfter816, gammaAfter816]
  exact numeric
theorem numeric817 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 192 p
  rw [at192] at beforeRange
  have afterRange := bonus_range 171 (HazardPattern.afterPattern 10000 p (.walk 171))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ∧ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ≤ 2 at afterRange
  rw [gammaAfter817] at afterRange
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
theorem local817 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 171) + NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 171))) + bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 171) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 192 p at decreasing
  rw [gammaAfter817, at192] at decreasing
  have numeric := numeric817 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171))
  rw [oldBefore192, at192, literal, oldAfter817, gammaAfter817]
  exact numeric
theorem numeric818 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 192 p
  rw [at192] at beforeRange
  have afterRange := bonus_range 169 (HazardPattern.afterPattern 10000 p (.walk 169))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ∧ bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) ≤ 2 at afterRange
  rw [gammaAfter818] at afterRange
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
theorem local818 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 169) + NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) + bonus 169 (HazardPattern.afterPattern 10000 p (.walk 169)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 169) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) < bonus 192 p at decreasing
  rw [gammaAfter818, at192] at decreasing
  have numeric := numeric818 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169))
  rw [oldBefore192, at192, literal, oldAfter818, gammaAfter818]
  exact numeric
theorem numeric819 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 192 p
  rw [at192] at beforeRange
  have afterRange := bonus_range 215 (HazardPattern.afterPattern 10000 p (.walk 215))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) ∧ bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) ≤ 2 at afterRange
  rw [gammaAfter819] at afterRange
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
theorem local819 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 215 (HazardPattern.afterPattern 10000 p (.walk 215)) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 215) + NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 215))) + bonus 215 (HazardPattern.afterPattern 10000 p (.walk 215)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 215) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) < bonus 192 p at decreasing
  rw [gammaAfter819, at192] at decreasing
  have numeric := numeric819 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215))
  rw [oldBefore192, at192, literal, oldAfter819, gammaAfter819]
  exact numeric
theorem numeric820 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 192 p
  rw [at192] at beforeRange
  have afterRange := bonus_range 213 (HazardPattern.afterPattern 10000 p (.walk 213))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) ∧ bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) ≤ 2 at afterRange
  rw [gammaAfter820] at afterRange
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
theorem local820 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 213 (HazardPattern.afterPattern 10000 p (.walk 213)) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 213) + NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 213))) + bonus 213 (HazardPattern.afterPattern 10000 p (.walk 213)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 213) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) < bonus 192 p at decreasing
  rw [gammaAfter820, at192] at decreasing
  have numeric := numeric820 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213))
  rw [oldBefore192, at192, literal, oldAfter820, gammaAfter820]
  exact numeric
theorem numeric821 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 193 p
  rw [at193] at beforeRange
  have afterRange := bonus_range 171 (HazardPattern.afterPattern 10000 p (.walk 171))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ∧ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ≤ 2 at afterRange
  rw [gammaAfter821] at afterRange
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
theorem local821 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 171) + NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 171))) + bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 171) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 193 p at decreasing
  rw [gammaAfter821, at193] at decreasing
  have numeric := numeric821 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171))
  rw [oldBefore193, at193, literal, oldAfter821, gammaAfter821]
  exact numeric
theorem numeric822 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 193 p
  rw [at193] at beforeRange
  have afterRange := bonus_range 171 (HazardPattern.afterPattern 10000 p (.push 171 (.stay 149)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 171 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 149))) ∧ bonus (HazardPattern.nextHero (.push 171 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 149))) ≤ 2 at afterRange
  rw [gammaAfter822] at afterRange
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
theorem local822 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 171 (HazardPattern.afterPattern 10000 p (.push 171 (.stay 149))) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 171 (.stay 149)) + NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 171 (.stay 149)))) + bonus 171 (HazardPattern.afterPattern 10000 p (.push 171 (.stay 149))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 171 (.stay 149)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 171 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 149))) < bonus 193 p at decreasing
  rw [gammaAfter822, at193] at decreasing
  have numeric := numeric822 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 171 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 149)))
  rw [oldBefore193, at193, literal, oldAfter822, gammaAfter822]
  exact numeric
theorem numeric823 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 193 p
  rw [at193] at beforeRange
  have afterRange := bonus_range 215 (HazardPattern.afterPattern 10000 p (.walk 215))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) ∧ bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) ≤ 2 at afterRange
  rw [gammaAfter823] at afterRange
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
theorem local823 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 215 (HazardPattern.afterPattern 10000 p (.walk 215)) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 215) + NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 215))) + bonus 215 (HazardPattern.afterPattern 10000 p (.walk 215)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 215) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) < bonus 193 p at decreasing
  rw [gammaAfter823, at193] at decreasing
  have numeric := numeric823 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215))
  rw [oldBefore193, at193, literal, oldAfter823, gammaAfter823]
  exact numeric
theorem numeric824 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 193 p
  rw [at193] at beforeRange
  have afterRange := bonus_range 194 (HazardPattern.afterPattern 10000 p (.walk 194))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) ∧ bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) ≤ 2 at afterRange
  rw [gammaAfter824] at afterRange
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
theorem local824 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 194 (HazardPattern.afterPattern 10000 p (.walk 194)) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 194) + NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 194))) + bonus 194 (HazardPattern.afterPattern 10000 p (.walk 194)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 194) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) < bonus 193 p at decreasing
  rw [gammaAfter824, at193] at decreasing
  have numeric := numeric824 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194))
  rw [oldBefore193, at193, literal, oldAfter824, gammaAfter824]
  exact numeric
theorem numeric825 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 193 p
  rw [at193] at beforeRange
  have afterRange := bonus_range 192 (HazardPattern.afterPattern 10000 p (.walk 192))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ∧ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ≤ 2 at afterRange
  rw [gammaAfter825] at afterRange
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
theorem local825 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 192) + NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 192))) + bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 192) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 193 p at decreasing
  rw [gammaAfter825, at193] at decreasing
  have numeric := numeric825 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192))
  rw [oldBefore193, at193, literal, oldAfter825, gammaAfter825]
  exact numeric
theorem numeric826 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 193 p
  rw [at193] at beforeRange
  have afterRange := bonus_range 192 (HazardPattern.afterPattern 10000 p (.push 192 (.stay 191)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 192 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 191))) ∧ bonus (HazardPattern.nextHero (.push 192 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 191))) ≤ 2 at afterRange
  rw [gammaAfter826] at afterRange
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
theorem local826 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 192 (HazardPattern.afterPattern 10000 p (.push 192 (.stay 191))) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 192 (.stay 191)) + NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 192 (.stay 191)))) + bonus 192 (HazardPattern.afterPattern 10000 p (.push 192 (.stay 191))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 192 (.stay 191)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 192 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 191))) < bonus 193 p at decreasing
  rw [gammaAfter826, at193] at decreasing
  have numeric := numeric826 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 192 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 191)))
  rw [oldBefore193, at193, literal, oldAfter826, gammaAfter826]
  exact numeric
theorem numeric827 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 193 p
  rw [at193] at beforeRange
  have afterRange := bonus_range 172 (HazardPattern.afterPattern 10000 p (.walk 172))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) ∧ bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) ≤ 2 at afterRange
  rw [gammaAfter827] at afterRange
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
theorem local827 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 172 (HazardPattern.afterPattern 10000 p (.walk 172)) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 172) + NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 172))) + bonus 172 (HazardPattern.afterPattern 10000 p (.walk 172)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 172) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) < bonus 193 p at decreasing
  rw [gammaAfter827, at193] at decreasing
  have numeric := numeric827 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172))
  rw [oldBefore193, at193, literal, oldAfter827, gammaAfter827]
  exact numeric
theorem numeric828 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 193 p
  rw [at193] at beforeRange
  have afterRange := bonus_range 170 (HazardPattern.afterPattern 10000 p (.walk 170))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ∧ bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) ≤ 2 at afterRange
  rw [gammaAfter828] at afterRange
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
theorem local828 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 170) + NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 170))) + bonus 170 (HazardPattern.afterPattern 10000 p (.walk 170)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 170) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) < bonus 193 p at decreasing
  rw [gammaAfter828, at193] at decreasing
  have numeric := numeric828 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170))
  rw [oldBefore193, at193, literal, oldAfter828, gammaAfter828]
  exact numeric
theorem numeric829 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 193 p
  rw [at193] at beforeRange
  have afterRange := bonus_range 216 (HazardPattern.afterPattern 10000 p (.walk 216))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 216)) (HazardPattern.afterPattern 10000 p (.walk 216)) ∧ bonus (HazardPattern.nextHero (.walk 216)) (HazardPattern.afterPattern 10000 p (.walk 216)) ≤ 2 at afterRange
  rw [gammaAfter829] at afterRange
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
theorem local829 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 216 (HazardPattern.afterPattern 10000 p (.walk 216)) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 216) + NetHack.Sokoban22Refined85.bonus 216 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 216))) + bonus 216 (HazardPattern.afterPattern 10000 p (.walk 216)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 216) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 216)) (HazardPattern.afterPattern 10000 p (.walk 216)) < bonus 193 p at decreasing
  rw [gammaAfter829, at193] at decreasing
  have numeric := numeric829 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 216)) (HazardPattern.afterPattern 10000 p (.walk 216))
  rw [oldBefore193, at193, literal, oldAfter829, gammaAfter829]
  exact numeric
theorem numeric830 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 193 p
  rw [at193] at beforeRange
  have afterRange := bonus_range 214 (HazardPattern.afterPattern 10000 p (.walk 214))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) ∧ bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) ≤ 2 at afterRange
  rw [gammaAfter830] at afterRange
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
theorem local830 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 214 (HazardPattern.afterPattern 10000 p (.walk 214)) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 214) + NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 214))) + bonus 214 (HazardPattern.afterPattern 10000 p (.walk 214)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 214) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) < bonus 193 p at decreasing
  rw [gammaAfter830, at193] at decreasing
  have numeric := numeric830 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214))
  rw [oldBefore193, at193, literal, oldAfter830, gammaAfter830]
  exact numeric
theorem numeric831 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 194 p
  rw [at194] at beforeRange
  have afterRange := bonus_range 172 (HazardPattern.afterPattern 10000 p (.walk 172))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) ∧ bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) ≤ 2 at afterRange
  rw [gammaAfter831] at afterRange
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
theorem local831 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 172 (HazardPattern.afterPattern 10000 p (.walk 172)) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 172) + NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 172))) + bonus 172 (HazardPattern.afterPattern 10000 p (.walk 172)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 172) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) < bonus 194 p at decreasing
  rw [gammaAfter831, at194] at decreasing
  have numeric := numeric831 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172))
  rw [oldBefore194, at194, literal, oldAfter831, gammaAfter831]
  exact numeric
theorem numeric832 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 194 p
  rw [at194] at beforeRange
  have afterRange := bonus_range 172 (HazardPattern.afterPattern 10000 p (.push 172 (.stay 150)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 172 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 172 (.stay 150))) ∧ bonus (HazardPattern.nextHero (.push 172 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 172 (.stay 150))) ≤ 2 at afterRange
  rw [gammaAfter832] at afterRange
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
theorem local832 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 172 (HazardPattern.afterPattern 10000 p (.push 172 (.stay 150))) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 172 (.stay 150)) + NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 172 (.stay 150)))) + bonus 172 (HazardPattern.afterPattern 10000 p (.push 172 (.stay 150))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 172 (.stay 150)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 172 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 172 (.stay 150))) < bonus 194 p at decreasing
  rw [gammaAfter832, at194] at decreasing
  have numeric := numeric832 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 172 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 172 (.stay 150)))
  rw [oldBefore194, at194, literal, oldAfter832, gammaAfter832]
  exact numeric
theorem numeric833 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 194 p
  rw [at194] at beforeRange
  have afterRange := bonus_range 216 (HazardPattern.afterPattern 10000 p (.walk 216))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 216)) (HazardPattern.afterPattern 10000 p (.walk 216)) ∧ bonus (HazardPattern.nextHero (.walk 216)) (HazardPattern.afterPattern 10000 p (.walk 216)) ≤ 2 at afterRange
  rw [gammaAfter833] at afterRange
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
theorem local833 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 216 (HazardPattern.afterPattern 10000 p (.walk 216)) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 216) + NetHack.Sokoban22Refined85.bonus 216 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 216))) + bonus 216 (HazardPattern.afterPattern 10000 p (.walk 216)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 216) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 216)) (HazardPattern.afterPattern 10000 p (.walk 216)) < bonus 194 p at decreasing
  rw [gammaAfter833, at194] at decreasing
  have numeric := numeric833 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 216)) (HazardPattern.afterPattern 10000 p (.walk 216))
  rw [oldBefore194, at194, literal, oldAfter833, gammaAfter833]
  exact numeric
theorem numeric834 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 194 p
  rw [at194] at beforeRange
  have afterRange := bonus_range 193 (HazardPattern.afterPattern 10000 p (.walk 193))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ∧ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ≤ 2 at afterRange
  rw [gammaAfter834] at afterRange
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
theorem local834 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 193) + NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 193))) + bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 193) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 194 p at decreasing
  rw [gammaAfter834, at194] at decreasing
  have numeric := numeric834 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193))
  rw [oldBefore194, at194, literal, oldAfter834, gammaAfter834]
  exact numeric
theorem numeric835 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 194 p
  rw [at194] at beforeRange
  have afterRange := bonus_range 193 (HazardPattern.afterPattern 10000 p (.push 193 (.stay 192)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 193 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 192))) ∧ bonus (HazardPattern.nextHero (.push 193 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 192))) ≤ 2 at afterRange
  rw [gammaAfter835] at afterRange
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
theorem local835 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 193 (HazardPattern.afterPattern 10000 p (.push 193 (.stay 192))) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 193 (.stay 192)) + NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 193 (.stay 192)))) + bonus 193 (HazardPattern.afterPattern 10000 p (.push 193 (.stay 192))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 193 (.stay 192)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 193 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 192))) < bonus 194 p at decreasing
  rw [gammaAfter835, at194] at decreasing
  have numeric := numeric835 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 193 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 192)))
  rw [oldBefore194, at194, literal, oldAfter835, gammaAfter835]
  exact numeric
theorem numeric836 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 194 p
  rw [at194] at beforeRange
  have afterRange := bonus_range 171 (HazardPattern.afterPattern 10000 p (.walk 171))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ∧ bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) ≤ 2 at afterRange
  rw [gammaAfter836] at afterRange
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
theorem local836 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 171) + NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 171))) + bonus 171 (HazardPattern.afterPattern 10000 p (.walk 171)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 171) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) < bonus 194 p at decreasing
  rw [gammaAfter836, at194] at decreasing
  have numeric := numeric836 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171))
  rw [oldBefore194, at194, literal, oldAfter836, gammaAfter836]
  exact numeric
theorem numeric837 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 194 p
  rw [at194] at beforeRange
  have afterRange := bonus_range 215 (HazardPattern.afterPattern 10000 p (.walk 215))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) ∧ bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) ≤ 2 at afterRange
  rw [gammaAfter837] at afterRange
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
theorem local837 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 215 (HazardPattern.afterPattern 10000 p (.walk 215)) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 215) + NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 215))) + bonus 215 (HazardPattern.afterPattern 10000 p (.walk 215)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 215) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) < bonus 194 p at decreasing
  rw [gammaAfter837, at194] at decreasing
  have numeric := numeric837 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215))
  rw [oldBefore194, at194, literal, oldAfter837, gammaAfter837]
  exact numeric
theorem numeric838 (p : Pattern) (guard : d194333 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 199 p
  rw [at199] at beforeRange
  have afterRange := bonus_range 177 (HazardPattern.afterPattern 10000 p (.walk 177))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) ∧ bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) ≤ 2 at afterRange
  rw [gammaAfter838] at afterRange
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
theorem local838 (p : Pattern) (guard : d194333 p = 1)
    (decreasing : bonus 177 (HazardPattern.afterPattern 10000 p (.walk 177)) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 177) + NetHack.Sokoban22Refined85.bonus 177 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 177))) + bonus 177 (HazardPattern.afterPattern 10000 p (.walk 177)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 177) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) < bonus 199 p at decreasing
  rw [gammaAfter838, at199] at decreasing
  have numeric := numeric838 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177))
  rw [oldBefore199, at199, literal, oldAfter838, gammaAfter838]
  exact numeric
theorem numeric839 (p : Pattern) (guard : d132769 p = 1) (decreasing : d0 p < d5849 p) :
    d47866 p + d5849 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 199 p
  rw [at199] at beforeRange
  have afterRange := bonus_range 177 (HazardPattern.afterPattern 10000 p (.push 177 (.stay 155)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 177 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 177 (.stay 155))) ∧ bonus (HazardPattern.nextHero (.push 177 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 177 (.stay 155))) ≤ 2 at afterRange
  rw [gammaAfter839] at afterRange
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
theorem local839 (p : Pattern) (guard : d132769 p = 1)
    (decreasing : bonus 177 (HazardPattern.afterPattern 10000 p (.push 177 (.stay 155))) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 177 (.stay 155)) + NetHack.Sokoban22Refined85.bonus 177 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 177 (.stay 155)))) + bonus 177 (HazardPattern.afterPattern 10000 p (.push 177 (.stay 155))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 177 (.stay 155)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 177 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 177 (.stay 155))) < bonus 199 p at decreasing
  rw [gammaAfter839, at199] at decreasing
  have numeric := numeric839 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 177 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 177 (.stay 155)))
  rw [oldBefore199, at199, literal, oldAfter839, gammaAfter839]
  exact numeric
end NetHack.Soko22Hazard87
