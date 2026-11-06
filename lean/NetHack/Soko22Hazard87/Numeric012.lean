import NetHack.Soko22Hazard87.Numeric011
import NetHack.Soko22Hazard87.AndIntroBlocks0281
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric840 (p : Pattern) (guard : d194336 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 199 p
  rw [at199] at beforeRange
  have afterRange := bonus_range 200 (HazardPattern.afterPattern 10000 p (.walk 200))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) ∧ bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) ≤ 2 at afterRange
  rw [gammaAfter840] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro55999 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro56000 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro56000 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local840 (p : Pattern) (guard : d194336 p = 1)
    (decreasing : bonus 200 (HazardPattern.afterPattern 10000 p (.walk 200)) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 200) + NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 200))) + bonus 200 (HazardPattern.afterPattern 10000 p (.walk 200)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 200) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) < bonus 199 p at decreasing
  rw [gammaAfter840, at199] at decreasing
  have numeric := numeric840 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200))
  rw [oldBefore199, at199, literal, oldAfter840, gammaAfter840]
  exact numeric
theorem numeric841 (p : Pattern) (guard : d227687 p = 1) (decreasing : d229483 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d229483 p := by
  have beforeRange := bonus_range 199 p
  rw [at199] at beforeRange
  have afterRange := bonus_range 200 (HazardPattern.afterPattern 10000 p (.push 200 (.stay 201)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 200 (.stay 201))) (HazardPattern.afterPattern 10000 p (.push 200 (.stay 201))) ∧ bonus (HazardPattern.nextHero (.push 200 (.stay 201))) (HazardPattern.afterPattern 10000 p (.push 200 (.stay 201))) ≤ 2 at afterRange
  rw [gammaAfter841] at afterRange
  have possibilities : (d5849 p = 1 ∧ d229483 p = 0) ∨ (d5849 p = 2 ∧ d229483 p = 0) ∨ (d5849 p = 2 ∧ d229483 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro22871 p pair.2
    have combined := andIntro56005 p beforeEq guard
    have complete := andIntro56006 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro22871 p pair.2
    have combined := andIntro56011 p beforeEq guard
    have complete := andIntro56006 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro22999 p pair.2
    have combined := andIntro56011 p beforeEq guard
    have complete := andIntro56012 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local841 (p : Pattern) (guard : d227687 p = 1)
    (decreasing : bonus 200 (HazardPattern.afterPattern 10000 p (.push 200 (.stay 201))) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 200 (.stay 201)) + NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 200 (.stay 201)))) + bonus 200 (HazardPattern.afterPattern 10000 p (.push 200 (.stay 201))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 200 (.stay 201)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 200 (.stay 201))) (HazardPattern.afterPattern 10000 p (.push 200 (.stay 201))) < bonus 199 p at decreasing
  rw [gammaAfter841, at199] at decreasing
  have numeric := numeric841 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 200 (.stay 201))) (HazardPattern.afterPattern 10000 p (.push 200 (.stay 201)))
  rw [oldBefore199, at199, literal, oldAfter841, gammaAfter841]
  exact numeric
theorem numeric842 (p : Pattern) (guard : d231166 p = 1) (decreasing : d25101 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d25101 p := by
  have beforeRange := bonus_range 200 p
  rw [at200] at beforeRange
  have afterRange := bonus_range 201 (HazardPattern.afterPattern 10000 p (.walk 201))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) ∧ bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) ≤ 2 at afterRange
  rw [gammaAfter842] at afterRange
  have possibilities : (d5849 p = 1 ∧ d25101 p = 0) ∨ (d5849 p = 2 ∧ d25101 p = 0) ∨ (d5849 p = 2 ∧ d25101 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro20211 p pair.2
    have combined := andIntro56311 p beforeEq guard
    have complete := andIntro56600 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro20211 p pair.2
    have combined := andIntro56632 p beforeEq guard
    have complete := andIntro56676 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro20354 p pair.2
    have combined := andIntro56632 p beforeEq guard
    have complete := andIntro56720 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local842 (p : Pattern) (guard : d231166 p = 1)
    (decreasing : bonus 201 (HazardPattern.afterPattern 10000 p (.walk 201)) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 201) + NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 201))) + bonus 201 (HazardPattern.afterPattern 10000 p (.walk 201)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 201) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) < bonus 200 p at decreasing
  rw [gammaAfter842, at200] at decreasing
  have numeric := numeric842 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201))
  rw [oldBefore200, at200, literal, oldAfter842, gammaAfter842]
  exact numeric
theorem numeric843 (p : Pattern) (guard : d231382 p = 1) (decreasing : d233261 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d233261 p := by
  have beforeRange := bonus_range 200 p
  rw [at200] at beforeRange
  have afterRange := bonus_range 201 (HazardPattern.afterPattern 10000 p (.push 201 (.stay 202)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 201 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 201 (.stay 202))) ∧ bonus (HazardPattern.nextHero (.push 201 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 201 (.stay 202))) ≤ 2 at afterRange
  rw [gammaAfter843] at afterRange
  have possibilities : (d5849 p = 1 ∧ d233261 p = 0) ∨ (d5849 p = 2 ∧ d233261 p = 0) ∨ (d5849 p = 2 ∧ d233261 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro23364 p pair.2
    have combined := andIntro57057 p beforeEq guard
    have complete := andIntro57336 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro23364 p pair.2
    have combined := andIntro57369 p beforeEq guard
    have complete := andIntro57413 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro23494 p pair.2
    have combined := andIntro57369 p beforeEq guard
    have complete := andIntro57457 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local843 (p : Pattern) (guard : d231382 p = 1)
    (decreasing : bonus 201 (HazardPattern.afterPattern 10000 p (.push 201 (.stay 202))) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 201 (.stay 202)) + NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 201 (.stay 202)))) + bonus 201 (HazardPattern.afterPattern 10000 p (.push 201 (.stay 202))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 201 (.stay 202)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 201 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 201 (.stay 202))) < bonus 200 p at decreasing
  rw [gammaAfter843, at200] at decreasing
  have numeric := numeric843 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 201 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 201 (.stay 202)))
  rw [oldBefore200, at200, literal, oldAfter843, gammaAfter843]
  exact numeric
theorem numeric844 (p : Pattern) (guard : d194336 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 200 p
  rw [at200] at beforeRange
  have afterRange := bonus_range 199 (HazardPattern.afterPattern 10000 p (.walk 199))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 199)) (HazardPattern.afterPattern 10000 p (.walk 199)) ∧ bonus (HazardPattern.nextHero (.walk 199)) (HazardPattern.afterPattern 10000 p (.walk 199)) ≤ 2 at afterRange
  rw [gammaAfter844] at afterRange
  have possibilities : (d5849 p = 1 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 0) ∨ (d5849 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro55999 p beforeEq guard
    have complete := andIntro9330 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro56000 p beforeEq guard
    have complete := andIntro6924 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro56000 p beforeEq guard
    have complete := andIntro6968 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local844 (p : Pattern) (guard : d194336 p = 1)
    (decreasing : bonus 199 (HazardPattern.afterPattern 10000 p (.walk 199)) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 199) + NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 199))) + bonus 199 (HazardPattern.afterPattern 10000 p (.walk 199)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 199) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 199)) (HazardPattern.afterPattern 10000 p (.walk 199)) < bonus 200 p at decreasing
  rw [gammaAfter844, at200] at decreasing
  have numeric := numeric844 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 199)) (HazardPattern.afterPattern 10000 p (.walk 199))
  rw [oldBefore200, at200, literal, oldAfter844, gammaAfter844]
  exact numeric
theorem numeric845 (p : Pattern) (guard : d194337 p = 1) (decreasing : d5849 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 200 p
  rw [at200] at beforeRange
  have afterRange := bonus_range 177 (HazardPattern.afterPattern 10000 p (.walk 177))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) ∧ bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) ≤ 2 at afterRange
  rw [gammaAfter845] at afterRange
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
theorem local845 (p : Pattern) (guard : d194337 p = 1)
    (decreasing : bonus 177 (HazardPattern.afterPattern 10000 p (.walk 177)) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 177) + NetHack.Sokoban22Refined85.bonus 177 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 177))) + bonus 177 (HazardPattern.afterPattern 10000 p (.walk 177)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 177) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) < bonus 200 p at decreasing
  rw [gammaAfter845, at200] at decreasing
  have numeric := numeric845 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177))
  rw [oldBefore200, at200, literal, oldAfter845, gammaAfter845]
  exact numeric
theorem numeric846 (p : Pattern) (guard : d236583 p = 1) (decreasing : d30634 p < d5849 p) :
    d47866 p + d5849 p ≤ (0 : Int) + d47866 p + d30634 p := by
  have beforeRange := bonus_range 200 p
  rw [at200] at beforeRange
  have afterRange := bonus_range 223 (HazardPattern.afterPattern 10000 p (.walk 223))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) ∧ bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) ≤ 2 at afterRange
  rw [gammaAfter846] at afterRange
  have possibilities : (d5849 p = 1 ∧ d30634 p = 0) ∨ (d5849 p = 2 ∧ d30634 p = 0) ∨ (d5849 p = 2 ∧ d30634 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro3469 p pair.1
    have afterEq := eqIntro23817 p pair.2
    have combined := andIntro57769 p beforeEq guard
    have complete := andIntro58085 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro23817 p pair.2
    have combined := andIntro58117 p beforeEq guard
    have complete := andIntro58161 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro4445 p pair.1
    have afterEq := eqIntro23933 p pair.2
    have combined := andIntro58117 p beforeEq guard
    have complete := andIntro58205 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local846 (p : Pattern) (guard : d236583 p = 1)
    (decreasing : bonus 223 (HazardPattern.afterPattern 10000 p (.walk 223)) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 223) + NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 223))) + bonus 223 (HazardPattern.afterPattern 10000 p (.walk 223)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 223) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) < bonus 200 p at decreasing
  rw [gammaAfter846, at200] at decreasing
  have numeric := numeric846 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223))
  rw [oldBefore200, at200, literal, oldAfter846, gammaAfter846]
  exact numeric
theorem numeric847 (p : Pattern) (guard : d236582 p = 1) (decreasing : d30634 p < d25101 p) :
    d47866 p + d25101 p ≤ (0 : Int) + d47866 p + d30634 p := by
  have beforeRange := bonus_range 201 p
  rw [at201] at beforeRange
  have afterRange := bonus_range 223 (HazardPattern.afterPattern 10000 p (.walk 223))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) ∧ bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) ≤ 2 at afterRange
  rw [gammaAfter847] at afterRange
  have possibilities : (d25101 p = 1 ∧ d30634 p = 0) ∨ (d25101 p = 2 ∧ d30634 p = 0) ∨ (d25101 p = 2 ∧ d30634 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20354 p pair.1
    have afterEq := eqIntro23817 p pair.2
    have combined := andIntro58374 p beforeEq guard
    have complete := andIntro58085 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro23817 p pair.2
    have combined := andIntro58394 p beforeEq guard
    have complete := andIntro58161 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro23933 p pair.2
    have combined := andIntro58394 p beforeEq guard
    have complete := andIntro58205 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local847 (p : Pattern) (guard : d236582 p = 1)
    (decreasing : bonus 223 (HazardPattern.afterPattern 10000 p (.walk 223)) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 223) + NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 223))) + bonus 223 (HazardPattern.afterPattern 10000 p (.walk 223)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 223) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) < bonus 201 p at decreasing
  rw [gammaAfter847, at201] at decreasing
  have numeric := numeric847 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223))
  rw [oldBefore201, at201, literal, oldAfter847, gammaAfter847]
  exact numeric
theorem numeric848 (p : Pattern) (guard : d239127 p = 1) (decreasing : d0 p < d25101 p) :
    d47866 p + d25101 p ≤ (5 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 201 p
  rw [at201] at beforeRange
  have afterRange := bonus_range 223 (HazardPattern.afterPattern 10000 p (.push 223 (.stay 245)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 223 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 223 (.stay 245))) ∧ bonus (HazardPattern.nextHero (.push 223 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 223 (.stay 245))) ≤ 2 at afterRange
  rw [gammaAfter848] at afterRange
  have possibilities : (d25101 p = 1 ∧ d0 p = 0) ∨ (d25101 p = 2 ∧ d0 p = 0) ∨ (d25101 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20354 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro58721 p beforeEq guard
    have complete := andIntro58722 p afterEq combined
    have bound := compare28885 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro58755 p beforeEq guard
    have complete := andIntro58756 p afterEq combined
    have bound := compare28886 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro58755 p beforeEq guard
    have complete := andIntro58757 p afterEq combined
    have bound := compare28887 p complete
    omega
theorem local848 (p : Pattern) (guard : d239127 p = 1)
    (decreasing : bonus 223 (HazardPattern.afterPattern 10000 p (.push 223 (.stay 245))) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 223 (.stay 245)) + NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 223 (.stay 245)))) + bonus 223 (HazardPattern.afterPattern 10000 p (.push 223 (.stay 245))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 223 (.stay 245)) = (5 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 223 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 223 (.stay 245))) < bonus 201 p at decreasing
  rw [gammaAfter848, at201] at decreasing
  have numeric := numeric848 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 223 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 223 (.stay 245)))
  rw [oldBefore201, at201, literal, oldAfter848, gammaAfter848]
  exact numeric
theorem numeric849 (p : Pattern) (guard : d208034 p = 1) (decreasing : d27480 p < d25101 p) :
    d47866 p + d25101 p ≤ (0 : Int) + d47866 p + d27480 p := by
  have beforeRange := bonus_range 201 p
  rw [at201] at beforeRange
  have afterRange := bonus_range 202 (HazardPattern.afterPattern 10000 p (.walk 202))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) ∧ bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) ≤ 2 at afterRange
  rw [gammaAfter849] at afterRange
  have possibilities : (d25101 p = 1 ∧ d27480 p = 0) ∨ (d25101 p = 2 ∧ d27480 p = 0) ∨ (d25101 p = 2 ∧ d27480 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20354 p pair.1
    have afterEq := eqIntro19116 p pair.2
    have combined := andIntro59062 p guard beforeEq
    have complete := andIntro59390 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro19116 p pair.2
    have combined := andIntro59422 p guard beforeEq
    have complete := andIntro59466 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro19271 p pair.2
    have combined := andIntro59422 p guard beforeEq
    have complete := andIntro59510 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local849 (p : Pattern) (guard : d208034 p = 1)
    (decreasing : bonus 202 (HazardPattern.afterPattern 10000 p (.walk 202)) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 202) + NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 202))) + bonus 202 (HazardPattern.afterPattern 10000 p (.walk 202)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 202) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) < bonus 201 p at decreasing
  rw [gammaAfter849, at201] at decreasing
  have numeric := numeric849 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202))
  rw [oldBefore201, at201, literal, oldAfter849, gammaAfter849]
  exact numeric
theorem numeric850 (p : Pattern) (guard : d231166 p = 1) (decreasing : d5849 p < d25101 p) :
    d47866 p + d25101 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 201 p
  rw [at201] at beforeRange
  have afterRange := bonus_range 200 (HazardPattern.afterPattern 10000 p (.walk 200))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) ∧ bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) ≤ 2 at afterRange
  rw [gammaAfter850] at afterRange
  have possibilities : (d25101 p = 1 ∧ d5849 p = 0) ∨ (d25101 p = 2 ∧ d5849 p = 0) ∨ (d25101 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20354 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro59511 p beforeEq guard
    have complete := andIntro59757 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro59758 p guard beforeEq
    have complete := andIntro59802 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro59758 p guard beforeEq
    have complete := andIntro59846 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local850 (p : Pattern) (guard : d231166 p = 1)
    (decreasing : bonus 200 (HazardPattern.afterPattern 10000 p (.walk 200)) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 200) + NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 200))) + bonus 200 (HazardPattern.afterPattern 10000 p (.walk 200)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 200) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) < bonus 201 p at decreasing
  rw [gammaAfter850, at201] at decreasing
  have numeric := numeric850 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200))
  rw [oldBefore201, at201, literal, oldAfter850, gammaAfter850]
  exact numeric
theorem numeric851 (p : Pattern) (guard : d227687 p = 1) (decreasing : d0 p < d25101 p) :
    d47866 p + d25101 p ≤ (5 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 201 p
  rw [at201] at beforeRange
  have afterRange := bonus_range 200 (HazardPattern.afterPattern 10000 p (.push 200 (.stay 199)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 200 (.stay 199))) (HazardPattern.afterPattern 10000 p (.push 200 (.stay 199))) ∧ bonus (HazardPattern.nextHero (.push 200 (.stay 199))) (HazardPattern.afterPattern 10000 p (.push 200 (.stay 199))) ≤ 2 at afterRange
  rw [gammaAfter851] at afterRange
  have possibilities : (d25101 p = 1 ∧ d0 p = 0) ∨ (d25101 p = 2 ∧ d0 p = 0) ∨ (d25101 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20354 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro59851 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare28887 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro59856 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare28888 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro59856 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare28887 p complete
    omega
theorem local851 (p : Pattern) (guard : d227687 p = 1)
    (decreasing : bonus 200 (HazardPattern.afterPattern 10000 p (.push 200 (.stay 199))) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 200 (.stay 199)) + NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 200 (.stay 199)))) + bonus 200 (HazardPattern.afterPattern 10000 p (.push 200 (.stay 199))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 200 (.stay 199)) = (5 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 200 (.stay 199))) (HazardPattern.afterPattern 10000 p (.push 200 (.stay 199))) < bonus 201 p at decreasing
  rw [gammaAfter851, at201] at decreasing
  have numeric := numeric851 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 200 (.stay 199))) (HazardPattern.afterPattern 10000 p (.push 200 (.stay 199)))
  rw [oldBefore201, at201, literal, oldAfter851, gammaAfter851]
  exact numeric
theorem numeric852 (p : Pattern) (guard : d208035 p = 1) (decreasing : d23134 p < d25101 p) :
    d47866 p + d25101 p ≤ (0 : Int) + d47866 p + d23134 p := by
  have beforeRange := bonus_range 201 p
  rw [at201] at beforeRange
  have afterRange := bonus_range 180 (HazardPattern.afterPattern 10000 p (.walk 180))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) ∧ bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) ≤ 2 at afterRange
  rw [gammaAfter852] at afterRange
  have possibilities : (d25101 p = 1 ∧ d23134 p = 0) ∨ (d25101 p = 2 ∧ d23134 p = 0) ∨ (d25101 p = 2 ∧ d23134 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20354 p pair.1
    have afterEq := eqIntro13202 p pair.2
    have combined := andIntro60160 p guard beforeEq
    have complete := andIntro60485 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro13202 p pair.2
    have combined := andIntro60517 p guard beforeEq
    have complete := andIntro60567 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro13358 p pair.2
    have combined := andIntro60517 p guard beforeEq
    have complete := andIntro60611 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local852 (p : Pattern) (guard : d208035 p = 1)
    (decreasing : bonus 180 (HazardPattern.afterPattern 10000 p (.walk 180)) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 180) + NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 180))) + bonus 180 (HazardPattern.afterPattern 10000 p (.walk 180)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 180) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) < bonus 201 p at decreasing
  rw [gammaAfter852, at201] at decreasing
  have numeric := numeric852 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180))
  rw [oldBefore201, at201, literal, oldAfter852, gammaAfter852]
  exact numeric
theorem numeric853 (p : Pattern) (guard : d241832 p = 1) (decreasing : d33212 p < d25101 p) :
    d47866 p + d25101 p ≤ (0 : Int) + d50101 p + d33212 p := by
  have beforeRange := bonus_range 201 p
  rw [at201] at beforeRange
  have afterRange := bonus_range 224 (HazardPattern.afterPattern 10000 p (.walk 224))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ∧ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ≤ 2 at afterRange
  rw [gammaAfter853] at afterRange
  have possibilities : (d25101 p = 1 ∧ d33212 p = 0) ∨ (d25101 p = 2 ∧ d33212 p = 0) ∨ (d25101 p = 2 ∧ d33212 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20354 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro60916 p beforeEq guard
    have complete := andIntro61257 p afterEq combined
    have bound := compare28889 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro61289 p beforeEq guard
    have complete := andIntro61338 p afterEq combined
    have bound := compare28890 p complete
    omega
  · have beforeEq := eqIntro24316 p pair.1
    have afterEq := eqIntro24937 p pair.2
    have combined := andIntro61289 p beforeEq guard
    have complete := andIntro61387 p combined afterEq
    have bound := compare28889 p complete
    omega
theorem local853 (p : Pattern) (guard : d241832 p = 1)
    (decreasing : bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 224) + NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 224))) + bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 224) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 201 p at decreasing
  rw [gammaAfter853, at201] at decreasing
  have numeric := numeric853 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224))
  rw [oldBefore201, at201, literal, oldAfter853, gammaAfter853]
  exact numeric
theorem numeric854 (p : Pattern) (guard : d198467 p = 1) (decreasing : d23134 p < d27480 p) :
    d47866 p + d27480 p ≤ (0 : Int) + d47866 p + d23134 p := by
  have beforeRange := bonus_range 202 p
  rw [at202] at beforeRange
  have afterRange := bonus_range 180 (HazardPattern.afterPattern 10000 p (.walk 180))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) ∧ bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) ≤ 2 at afterRange
  rw [gammaAfter854] at afterRange
  have possibilities : (d27480 p = 1 ∧ d23134 p = 0) ∨ (d27480 p = 2 ∧ d23134 p = 0) ∨ (d27480 p = 2 ∧ d23134 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro19271 p pair.1
    have afterEq := eqIntro13202 p pair.2
    have combined := andIntro61709 p guard beforeEq
    have complete := andIntro62022 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro13202 p pair.2
    have combined := andIntro62054 p guard beforeEq
    have complete := andIntro62104 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro13358 p pair.2
    have combined := andIntro62054 p guard beforeEq
    have complete := andIntro62148 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local854 (p : Pattern) (guard : d198467 p = 1)
    (decreasing : bonus 180 (HazardPattern.afterPattern 10000 p (.walk 180)) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 180) + NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 180))) + bonus 180 (HazardPattern.afterPattern 10000 p (.walk 180)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 180) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) < bonus 202 p at decreasing
  rw [gammaAfter854, at202] at decreasing
  have numeric := numeric854 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180))
  rw [oldBefore202, at202, literal, oldAfter854, gammaAfter854]
  exact numeric
theorem numeric855 (p : Pattern) (guard : d152855 p = 1) (decreasing : d247398 p < d27480 p) :
    d47866 p + d27480 p ≤ (2 : Int) + d47866 p + d247398 p := by
  have beforeRange := bonus_range 202 p
  rw [at202] at beforeRange
  have afterRange := bonus_range 180 (HazardPattern.afterPattern 10000 p (.push 180 (.stay 158)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 180 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 180 (.stay 158))) ∧ bonus (HazardPattern.nextHero (.push 180 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 180 (.stay 158))) ≤ 2 at afterRange
  rw [gammaAfter855] at afterRange
  have possibilities : (d27480 p = 1 ∧ d247398 p = 0) ∨ (d27480 p = 2 ∧ d247398 p = 0) ∨ (d27480 p = 2 ∧ d247398 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro19271 p pair.1
    have afterEq := eqIntro25675 p pair.2
    have combined := andIntro62467 p guard beforeEq
    have complete := andIntro62750 p afterEq combined
    have bound := compare28891 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro25675 p pair.2
    have combined := andIntro62782 p guard beforeEq
    have complete := andIntro62826 p afterEq combined
    have bound := compare28892 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro25792 p pair.2
    have combined := andIntro62782 p guard beforeEq
    have complete := andIntro62870 p combined afterEq
    have bound := compare10066 p complete
    omega
theorem local855 (p : Pattern) (guard : d152855 p = 1)
    (decreasing : bonus 180 (HazardPattern.afterPattern 10000 p (.push 180 (.stay 158))) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 180 (.stay 158)) + NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 180 (.stay 158)))) + bonus 180 (HazardPattern.afterPattern 10000 p (.push 180 (.stay 158))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 180 (.stay 158)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 180 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 180 (.stay 158))) < bonus 202 p at decreasing
  rw [gammaAfter855, at202] at decreasing
  have numeric := numeric855 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 180 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 180 (.stay 158)))
  rw [oldBefore202, at202, literal, oldAfter855, gammaAfter855]
  exact numeric
theorem numeric856 (p : Pattern) (guard : d251389 p = 1) (decreasing : d33212 p < d27480 p) :
    d47866 p + d27480 p ≤ (0 : Int) + d50101 p + d33212 p := by
  have beforeRange := bonus_range 202 p
  rw [at202] at beforeRange
  have afterRange := bonus_range 224 (HazardPattern.afterPattern 10000 p (.walk 224))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ∧ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ≤ 2 at afterRange
  rw [gammaAfter856] at afterRange
  have possibilities : (d27480 p = 1 ∧ d33212 p = 0) ∨ (d27480 p = 2 ∧ d33212 p = 0) ∨ (d27480 p = 2 ∧ d33212 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro19271 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro63195 p beforeEq guard
    have complete := andIntro63526 p afterEq combined
    have bound := compare28889 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro63558 p beforeEq guard
    have complete := andIntro63602 p afterEq combined
    have bound := compare28890 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro24937 p pair.2
    have combined := andIntro63558 p beforeEq guard
    have complete := andIntro63646 p afterEq combined
    have bound := compare28889 p complete
    omega
theorem local856 (p : Pattern) (guard : d251389 p = 1)
    (decreasing : bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 224) + NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 224))) + bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 224) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 202 p at decreasing
  rw [gammaAfter856, at202] at decreasing
  have numeric := numeric856 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224))
  rw [oldBefore202, at202, literal, oldAfter856, gammaAfter856]
  exact numeric
theorem numeric857 (p : Pattern) (guard : d253272 p = 1) (decreasing : d255612 p < d27480 p) :
    d47866 p + d27480 p ≤ (0 : Int) + d253503 p + d255612 p := by
  have beforeRange := bonus_range 202 p
  rw [at202] at beforeRange
  have afterRange := bonus_range 224 (HazardPattern.afterPattern 10000 p (.push 224 (.stay 246)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 224 (.stay 246))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 246))) ∧ bonus (HazardPattern.nextHero (.push 224 (.stay 246))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 246))) ≤ 2 at afterRange
  rw [gammaAfter857] at afterRange
  have possibilities : (d27480 p = 1 ∧ d255612 p = 0) ∨ (d27480 p = 2 ∧ d255612 p = 0) ∨ (d27480 p = 2 ∧ d255612 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro19271 p pair.1
    have afterEq := eqIntro26173 p pair.2
    have combined := andIntro64025 p beforeEq guard
    have complete := andIntro64314 p afterEq combined
    have bound := compare30766 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro26173 p pair.2
    have combined := andIntro64347 p beforeEq guard
    have complete := andIntro64391 p afterEq combined
    have bound := compare31946 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro26315 p pair.2
    have combined := andIntro64347 p beforeEq guard
    have complete := andIntro64435 p combined afterEq
    have bound := compare28893 p complete
    omega
theorem local857 (p : Pattern) (guard : d253272 p = 1)
    (decreasing : bonus 224 (HazardPattern.afterPattern 10000 p (.push 224 (.stay 246))) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 224 (.stay 246)) + NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 224 (.stay 246)))) + bonus 224 (HazardPattern.afterPattern 10000 p (.push 224 (.stay 246))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 224 (.stay 246)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 224 (.stay 246))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 246))) < bonus 202 p at decreasing
  rw [gammaAfter857, at202] at decreasing
  have numeric := numeric857 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 224 (.stay 246))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 246)))
  rw [oldBefore202, at202, literal, oldAfter857, gammaAfter857]
  exact numeric
theorem numeric858 (p : Pattern) (guard : d208034 p = 1) (decreasing : d25101 p < d27480 p) :
    d47866 p + d27480 p ≤ (0 : Int) + d47866 p + d25101 p := by
  have beforeRange := bonus_range 202 p
  rw [at202] at beforeRange
  have afterRange := bonus_range 201 (HazardPattern.afterPattern 10000 p (.walk 201))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) ∧ bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) ≤ 2 at afterRange
  rw [gammaAfter858] at afterRange
  have possibilities : (d27480 p = 1 ∧ d25101 p = 0) ∨ (d27480 p = 2 ∧ d25101 p = 0) ∨ (d27480 p = 2 ∧ d25101 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro19271 p pair.1
    have afterEq := eqIntro20211 p pair.2
    have combined := andIntro64749 p beforeEq guard
    have complete := andIntro65050 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro20211 p pair.2
    have combined := andIntro65082 p guard beforeEq
    have complete := andIntro65126 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro20354 p pair.2
    have combined := andIntro65082 p guard beforeEq
    have complete := andIntro65170 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local858 (p : Pattern) (guard : d208034 p = 1)
    (decreasing : bonus 201 (HazardPattern.afterPattern 10000 p (.walk 201)) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 201) + NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 201))) + bonus 201 (HazardPattern.afterPattern 10000 p (.walk 201)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 201) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) < bonus 202 p at decreasing
  rw [gammaAfter858, at202] at decreasing
  have numeric := numeric858 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201))
  rw [oldBefore202, at202, literal, oldAfter858, gammaAfter858]
  exact numeric
theorem numeric859 (p : Pattern) (guard : d231382 p = 1) (decreasing : d0 p < d27480 p) :
    d47866 p + d27480 p ≤ (2 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 202 p
  rw [at202] at beforeRange
  have afterRange := bonus_range 201 (HazardPattern.afterPattern 10000 p (.push 201 (.stay 200)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 201 (.stay 200))) (HazardPattern.afterPattern 10000 p (.push 201 (.stay 200))) ∧ bonus (HazardPattern.nextHero (.push 201 (.stay 200))) (HazardPattern.afterPattern 10000 p (.push 201 (.stay 200))) ≤ 2 at afterRange
  rw [gammaAfter859] at afterRange
  have possibilities : (d27480 p = 1 ∧ d0 p = 0) ∨ (d27480 p = 2 ∧ d0 p = 0) ∨ (d27480 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro19271 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro65498 p beforeEq guard
    have complete := andIntro65499 p afterEq combined
    have bound := compare31947 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro65531 p guard beforeEq
    have complete := andIntro65532 p afterEq combined
    have bound := compare31948 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro65531 p guard beforeEq
    have complete := andIntro65533 p afterEq combined
    have bound := compare10066 p complete
    omega
theorem local859 (p : Pattern) (guard : d231382 p = 1)
    (decreasing : bonus 201 (HazardPattern.afterPattern 10000 p (.push 201 (.stay 200))) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 201 (.stay 200)) + NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 201 (.stay 200)))) + bonus 201 (HazardPattern.afterPattern 10000 p (.push 201 (.stay 200))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 201 (.stay 200)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 201 (.stay 200))) (HazardPattern.afterPattern 10000 p (.push 201 (.stay 200))) < bonus 202 p at decreasing
  rw [gammaAfter859, at202] at decreasing
  have numeric := numeric859 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 201 (.stay 200))) (HazardPattern.afterPattern 10000 p (.push 201 (.stay 200)))
  rw [oldBefore202, at202, literal, oldAfter859, gammaAfter859]
  exact numeric
theorem numeric860 (p : Pattern) (guard : d212559 p = 1) (decreasing : d17560 p < d27480 p) :
    d47866 p + d27480 p ≤ (0 : Int) + d47866 p + d17560 p := by
  have beforeRange := bonus_range 202 p
  rw [at202] at beforeRange
  have afterRange := bonus_range 181 (HazardPattern.afterPattern 10000 p (.walk 181))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ∧ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ≤ 2 at afterRange
  rw [gammaAfter860] at afterRange
  have possibilities : (d27480 p = 1 ∧ d17560 p = 0) ∨ (d27480 p = 2 ∧ d17560 p = 0) ∨ (d27480 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro19271 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro65538 p beforeEq guard
    have complete := andIntro65864 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro65869 p guard beforeEq
    have complete := andIntro65919 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro65869 p guard beforeEq
    have complete := andIntro65963 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local860 (p : Pattern) (guard : d212559 p = 1)
    (decreasing : bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 181) + NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 181))) + bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 181) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 202 p at decreasing
  rw [gammaAfter860, at202] at decreasing
  have numeric := numeric860 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181))
  rw [oldBefore202, at202, literal, oldAfter860, gammaAfter860]
  exact numeric
theorem numeric861 (p : Pattern) (guard : d261986 p = 1) (decreasing : d36004 p < d27480 p) :
    d47866 p + d27480 p ≤ (0 : Int) + d50493 p + d36004 p := by
  have beforeRange := bonus_range 202 p
  rw [at202] at beforeRange
  have afterRange := bonus_range 225 (HazardPattern.afterPattern 10000 p (.walk 225))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ∧ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ≤ 2 at afterRange
  rw [gammaAfter861] at afterRange
  have possibilities : (d27480 p = 1 ∧ d36004 p = 0) ∨ (d27480 p = 2 ∧ d36004 p = 0) ∨ (d27480 p = 2 ∧ d36004 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro19271 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro66313 p beforeEq guard
    have complete := andIntro66657 p afterEq combined
    have bound := compare31949 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro66689 p beforeEq guard
    have complete := andIntro66744 p afterEq combined
    have bound := compare31950 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro26978 p pair.2
    have combined := andIntro66689 p beforeEq guard
    have complete := andIntro66793 p combined afterEq
    have bound := compare31949 p complete
    omega
theorem local861 (p : Pattern) (guard : d261986 p = 1)
    (decreasing : bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 225) + NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 225))) + bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 225) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 202 p at decreasing
  rw [gammaAfter861, at202] at decreasing
  have numeric := numeric861 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225))
  rw [oldBefore202, at202, literal, oldAfter861, gammaAfter861]
  exact numeric
theorem numeric862 (p : Pattern) (guard : d266246 p = 1) (decreasing : d30634 p < d27480 p) :
    d47866 p + d27480 p ≤ (0 : Int) + d47866 p + d30634 p := by
  have beforeRange := bonus_range 202 p
  rw [at202] at beforeRange
  have afterRange := bonus_range 223 (HazardPattern.afterPattern 10000 p (.walk 223))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) ∧ bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) ≤ 2 at afterRange
  rw [gammaAfter862] at afterRange
  have possibilities : (d27480 p = 1 ∧ d30634 p = 0) ∨ (d27480 p = 2 ∧ d30634 p = 0) ∨ (d27480 p = 2 ∧ d30634 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro19271 p pair.1
    have afterEq := eqIntro23817 p pair.2
    have combined := andIntro67075 p beforeEq guard
    have complete := andIntro67396 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro23817 p pair.2
    have combined := andIntro67424 p beforeEq guard
    have complete := andIntro67468 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro25370 p pair.1
    have afterEq := eqIntro23933 p pair.2
    have combined := andIntro67424 p beforeEq guard
    have complete := andIntro67512 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local862 (p : Pattern) (guard : d266246 p = 1)
    (decreasing : bonus 223 (HazardPattern.afterPattern 10000 p (.walk 223)) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 223) + NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 223))) + bonus 223 (HazardPattern.afterPattern 10000 p (.walk 223)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 223) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) < bonus 202 p at decreasing
  rw [gammaAfter862, at202] at decreasing
  have numeric := numeric862 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223))
  rw [oldBefore202, at202, literal, oldAfter862, gammaAfter862]
  exact numeric
theorem numeric863 (p : Pattern) (guard : d211415 p = 1) (decreasing : d17560 p < d28738 p) :
    d49782 p + d28738 p ≤ (0 : Int) + d49280 p + d17560 p := by
  have beforeRange := bonus_range 204 p
  rw [at204] at beforeRange
  have afterRange := bonus_range 182 (HazardPattern.afterPattern 10000 p (.walk 182))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) ∧ bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) ≤ 2 at afterRange
  rw [gammaAfter863] at afterRange
  have possibilities : (d28738 p = 1 ∧ d17560 p = 0) ∨ (d28738 p = 2 ∧ d17560 p = 0) ∨ (d28738 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20627 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro67513 p guard beforeEq
    have complete := andIntro67658 p afterEq combined
    have bound := compare31951 p complete
    omega
  · have beforeEq := eqIntro27177 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro67659 p guard beforeEq
    have complete := andIntro67683 p afterEq combined
    have bound := compare31952 p complete
    omega
  · have beforeEq := eqIntro27177 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro67659 p guard beforeEq
    have complete := andIntro67703 p afterEq combined
    have bound := compare31951 p complete
    omega
theorem local863 (p : Pattern) (guard : d211415 p = 1)
    (decreasing : bonus 182 (HazardPattern.afterPattern 10000 p (.walk 182)) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 182) + NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 182))) + bonus 182 (HazardPattern.afterPattern 10000 p (.walk 182)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 182) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) < bonus 204 p at decreasing
  rw [gammaAfter863, at204] at decreasing
  have numeric := numeric863 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182))
  rw [oldBefore204, at204, literal, oldAfter863, gammaAfter863]
  exact numeric
theorem numeric864 (p : Pattern) (guard : d171300 p = 1) (decreasing : d0 p < d28738 p) :
    d49782 p + d28738 p ≤ (2 : Int) + d267843 p + d0 p := by
  have beforeRange := bonus_range 204 p
  rw [at204] at beforeRange
  have afterRange := bonus_range 182 (HazardPattern.afterPattern 10000 p (.push 182 (.stay 160)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 182 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 182 (.stay 160))) ∧ bonus (HazardPattern.nextHero (.push 182 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 182 (.stay 160))) ≤ 2 at afterRange
  rw [gammaAfter864] at afterRange
  have possibilities : (d28738 p = 1 ∧ d0 p = 0) ∨ (d28738 p = 2 ∧ d0 p = 0) ∨ (d28738 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20627 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro67848 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare31953 p complete
    omega
  · have beforeEq := eqIntro27177 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro67868 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare31954 p complete
    omega
  · have beforeEq := eqIntro27177 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro67868 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare31953 p complete
    omega
theorem local864 (p : Pattern) (guard : d171300 p = 1)
    (decreasing : bonus 182 (HazardPattern.afterPattern 10000 p (.push 182 (.stay 160))) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 182 (.stay 160)) + NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 182 (.stay 160)))) + bonus 182 (HazardPattern.afterPattern 10000 p (.push 182 (.stay 160))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 182 (.stay 160)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 182 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 182 (.stay 160))) < bonus 204 p at decreasing
  rw [gammaAfter864, at204] at decreasing
  have numeric := numeric864 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 182 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 182 (.stay 160)))
  rw [oldBefore204, at204, literal, oldAfter864, gammaAfter864]
  exact numeric
theorem numeric865 (p : Pattern) (guard : d267844 p = 1) (decreasing : d38812 p < d28738 p) :
    d49782 p + d28738 p ≤ (0 : Int) + d50823 p + d38812 p := by
  have beforeRange := bonus_range 204 p
  rw [at204] at beforeRange
  have afterRange := bonus_range 226 (HazardPattern.afterPattern 10000 p (.walk 226))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) ∧ bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) ≤ 2 at afterRange
  rw [gammaAfter865] at afterRange
  have possibilities : (d28738 p = 1 ∧ d38812 p = 0) ∨ (d28738 p = 2 ∧ d38812 p = 0) ∨ (d28738 p = 2 ∧ d38812 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20627 p pair.1
    have afterEq := eqIntro27657 p pair.2
    have combined := andIntro68238 p beforeEq guard
    have complete := andIntro68589 p afterEq combined
    have bound := compare31955 p complete
    omega
  · have beforeEq := eqIntro27177 p pair.1
    have afterEq := eqIntro27657 p pair.2
    have combined := andIntro68627 p beforeEq guard
    have complete := andIntro68684 p afterEq combined
    have bound := compare31956 p complete
    omega
  · have beforeEq := eqIntro27177 p pair.1
    have afterEq := eqIntro27833 p pair.2
    have combined := andIntro68627 p beforeEq guard
    have complete := andIntro68733 p combined afterEq
    have bound := compare31955 p complete
    omega
theorem local865 (p : Pattern) (guard : d267844 p = 1)
    (decreasing : bonus 226 (HazardPattern.afterPattern 10000 p (.walk 226)) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 226) + NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 226))) + bonus 226 (HazardPattern.afterPattern 10000 p (.walk 226)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 226) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) < bonus 204 p at decreasing
  rw [gammaAfter865, at204] at decreasing
  have numeric := numeric865 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226))
  rw [oldBefore204, at204, literal, oldAfter865, gammaAfter865]
  exact numeric
theorem numeric866 (p : Pattern) (guard : d271212 p = 1) (decreasing : d273694 p < d28738 p) :
    d49782 p + d28738 p ≤ (0 : Int) + d50823 p + d273694 p := by
  have beforeRange := bonus_range 204 p
  rw [at204] at beforeRange
  have afterRange := bonus_range 226 (HazardPattern.afterPattern 10000 p (.push 226 (.stay 248)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 226 (.stay 248))) (HazardPattern.afterPattern 10000 p (.push 226 (.stay 248))) ∧ bonus (HazardPattern.nextHero (.push 226 (.stay 248))) (HazardPattern.afterPattern 10000 p (.push 226 (.stay 248))) ≤ 2 at afterRange
  rw [gammaAfter866] at afterRange
  have possibilities : (d28738 p = 1 ∧ d273694 p = 0) ∨ (d28738 p = 2 ∧ d273694 p = 0) ∨ (d28738 p = 2 ∧ d273694 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20627 p pair.1
    have afterEq := eqIntro28262 p pair.2
    have combined := andIntro69137 p beforeEq guard
    have complete := andIntro69457 p afterEq combined
    have bound := compare31955 p complete
    omega
  · have beforeEq := eqIntro27177 p pair.1
    have afterEq := eqIntro28262 p pair.2
    have combined := andIntro69496 p beforeEq guard
    have complete := andIntro69545 p afterEq combined
    have bound := compare31956 p complete
    omega
  · have beforeEq := eqIntro27177 p pair.1
    have afterEq := eqIntro28420 p pair.2
    have combined := andIntro69496 p beforeEq guard
    have complete := andIntro69589 p combined afterEq
    have bound := compare31955 p complete
    omega
theorem local866 (p : Pattern) (guard : d271212 p = 1)
    (decreasing : bonus 226 (HazardPattern.afterPattern 10000 p (.push 226 (.stay 248))) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 226 (.stay 248)) + NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 226 (.stay 248)))) + bonus 226 (HazardPattern.afterPattern 10000 p (.push 226 (.stay 248))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 226 (.stay 248)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 226 (.stay 248))) (HazardPattern.afterPattern 10000 p (.push 226 (.stay 248))) < bonus 204 p at decreasing
  rw [gammaAfter866, at204] at decreasing
  have numeric := numeric866 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 226 (.stay 248))) (HazardPattern.afterPattern 10000 p (.push 226 (.stay 248)))
  rw [oldBefore204, at204, literal, oldAfter866, gammaAfter866]
  exact numeric
theorem numeric867 (p : Pattern) (guard : d211416 p = 1) (decreasing : d17560 p < d28738 p) :
    d49782 p + d28738 p ≤ (0 : Int) + d47866 p + d17560 p := by
  have beforeRange := bonus_range 204 p
  rw [at204] at beforeRange
  have afterRange := bonus_range 181 (HazardPattern.afterPattern 10000 p (.walk 181))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ∧ bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) ≤ 2 at afterRange
  rw [gammaAfter867] at afterRange
  have possibilities : (d28738 p = 1 ∧ d17560 p = 0) ∨ (d28738 p = 2 ∧ d17560 p = 0) ∨ (d28738 p = 2 ∧ d17560 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20627 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro69590 p guard beforeEq
    have complete := andIntro67658 p afterEq combined
    have bound := compare31957 p complete
    omega
  · have beforeEq := eqIntro27177 p pair.1
    have afterEq := eqIntro10154 p pair.2
    have combined := andIntro69591 p guard beforeEq
    have complete := andIntro67683 p afterEq combined
    have bound := compare31958 p complete
    omega
  · have beforeEq := eqIntro27177 p pair.1
    have afterEq := eqIntro10254 p pair.2
    have combined := andIntro69591 p guard beforeEq
    have complete := andIntro67703 p afterEq combined
    have bound := compare31957 p complete
    omega
theorem local867 (p : Pattern) (guard : d211416 p = 1)
    (decreasing : bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 181) + NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 181))) + bonus 181 (HazardPattern.afterPattern 10000 p (.walk 181)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 181) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) < bonus 204 p at decreasing
  rw [gammaAfter867, at204] at decreasing
  have numeric := numeric867 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181))
  rw [oldBefore204, at204, literal, oldAfter867, gammaAfter867]
  exact numeric
theorem numeric868 (p : Pattern) (guard : d277740 p = 1) (decreasing : d36004 p < d28738 p) :
    d49782 p + d28738 p ≤ (0 : Int) + d50493 p + d36004 p := by
  have beforeRange := bonus_range 204 p
  rw [at204] at beforeRange
  have afterRange := bonus_range 225 (HazardPattern.afterPattern 10000 p (.walk 225))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ∧ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ≤ 2 at afterRange
  rw [gammaAfter868] at afterRange
  have possibilities : (d28738 p = 1 ∧ d36004 p = 0) ∨ (d28738 p = 2 ∧ d36004 p = 0) ∨ (d28738 p = 2 ∧ d36004 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro20627 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro69963 p beforeEq guard
    have complete := andIntro70313 p afterEq combined
    have bound := compare31959 p complete
    omega
  · have beforeEq := eqIntro27177 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro70351 p beforeEq guard
    have complete := andIntro70401 p afterEq combined
    have bound := compare31960 p complete
    omega
  · have beforeEq := eqIntro27177 p pair.1
    have afterEq := eqIntro26978 p pair.2
    have combined := andIntro70351 p beforeEq guard
    have complete := andIntro70445 p afterEq combined
    have bound := compare31959 p complete
    omega
theorem local868 (p : Pattern) (guard : d277740 p = 1)
    (decreasing : bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 225) + NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 225))) + bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 225) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 204 p at decreasing
  rw [gammaAfter868, at204] at decreasing
  have numeric := numeric868 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225))
  rw [oldBefore204, at204, literal, oldAfter868, gammaAfter868]
  exact numeric
theorem numeric869 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 210 p
  rw [at210] at beforeRange
  have afterRange := bonus_range 188 (HazardPattern.afterPattern 10000 p (.walk 188))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) ∧ bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) ≤ 2 at afterRange
  rw [gammaAfter869] at afterRange
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
theorem local869 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 188 (HazardPattern.afterPattern 10000 p (.walk 188)) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 188) + NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 188))) + bonus 188 (HazardPattern.afterPattern 10000 p (.walk 188)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 188) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) < bonus 210 p at decreasing
  rw [gammaAfter869, at210] at decreasing
  have numeric := numeric869 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188))
  rw [oldBefore210, at210, literal, oldAfter869, gammaAfter869]
  exact numeric
theorem numeric870 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 210 p
  rw [at210] at beforeRange
  have afterRange := bonus_range 188 (HazardPattern.afterPattern 10000 p (.push 188 (.stay 166)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 188 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 188 (.stay 166))) ∧ bonus (HazardPattern.nextHero (.push 188 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 188 (.stay 166))) ≤ 2 at afterRange
  rw [gammaAfter870] at afterRange
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
theorem local870 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 188 (HazardPattern.afterPattern 10000 p (.push 188 (.stay 166))) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 188 (.stay 166)) + NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 188 (.stay 166)))) + bonus 188 (HazardPattern.afterPattern 10000 p (.push 188 (.stay 166))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 188 (.stay 166)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 188 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 188 (.stay 166))) < bonus 210 p at decreasing
  rw [gammaAfter870, at210] at decreasing
  have numeric := numeric870 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 188 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 188 (.stay 166)))
  rw [oldBefore210, at210, literal, oldAfter870, gammaAfter870]
  exact numeric
theorem numeric871 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 210 p
  rw [at210] at beforeRange
  have afterRange := bonus_range 211 (HazardPattern.afterPattern 10000 p (.walk 211))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) ∧ bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) ≤ 2 at afterRange
  rw [gammaAfter871] at afterRange
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
theorem local871 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 211 (HazardPattern.afterPattern 10000 p (.walk 211)) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 211) + NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 211))) + bonus 211 (HazardPattern.afterPattern 10000 p (.walk 211)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 211) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) < bonus 210 p at decreasing
  rw [gammaAfter871, at210] at decreasing
  have numeric := numeric871 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211))
  rw [oldBefore210, at210, literal, oldAfter871, gammaAfter871]
  exact numeric
theorem numeric872 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 210 p
  rw [at210] at beforeRange
  have afterRange := bonus_range 211 (HazardPattern.afterPattern 10000 p (.push 211 (.stay 212)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 211 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 211 (.stay 212))) ∧ bonus (HazardPattern.nextHero (.push 211 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 211 (.stay 212))) ≤ 2 at afterRange
  rw [gammaAfter872] at afterRange
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
theorem local872 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 211 (HazardPattern.afterPattern 10000 p (.push 211 (.stay 212))) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 211 (.stay 212)) + NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 211 (.stay 212)))) + bonus 211 (HazardPattern.afterPattern 10000 p (.push 211 (.stay 212))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 211 (.stay 212)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 211 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 211 (.stay 212))) < bonus 210 p at decreasing
  rw [gammaAfter872, at210] at decreasing
  have numeric := numeric872 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 211 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 211 (.stay 212)))
  rw [oldBefore210, at210, literal, oldAfter872, gammaAfter872]
  exact numeric
theorem numeric873 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 210 p
  rw [at210] at beforeRange
  have afterRange := bonus_range 189 (HazardPattern.afterPattern 10000 p (.walk 189))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ∧ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ≤ 2 at afterRange
  rw [gammaAfter873] at afterRange
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
theorem local873 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 189) + NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 189))) + bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 189) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 210 p at decreasing
  rw [gammaAfter873, at210] at decreasing
  have numeric := numeric873 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189))
  rw [oldBefore210, at210, literal, oldAfter873, gammaAfter873]
  exact numeric
theorem numeric874 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 211 p
  rw [at211] at beforeRange
  have afterRange := bonus_range 189 (HazardPattern.afterPattern 10000 p (.walk 189))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ∧ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ≤ 2 at afterRange
  rw [gammaAfter874] at afterRange
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
theorem local874 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 189) + NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 189))) + bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 189) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 211 p at decreasing
  rw [gammaAfter874, at211] at decreasing
  have numeric := numeric874 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189))
  rw [oldBefore211, at211, literal, oldAfter874, gammaAfter874]
  exact numeric
theorem numeric875 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 211 p
  rw [at211] at beforeRange
  have afterRange := bonus_range 189 (HazardPattern.afterPattern 10000 p (.push 189 (.stay 167)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 189 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 167))) ∧ bonus (HazardPattern.nextHero (.push 189 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 167))) ≤ 2 at afterRange
  rw [gammaAfter875] at afterRange
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
theorem local875 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 189 (HazardPattern.afterPattern 10000 p (.push 189 (.stay 167))) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 189 (.stay 167)) + NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 189 (.stay 167)))) + bonus 189 (HazardPattern.afterPattern 10000 p (.push 189 (.stay 167))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 189 (.stay 167)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 189 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 167))) < bonus 211 p at decreasing
  rw [gammaAfter875, at211] at decreasing
  have numeric := numeric875 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 189 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 167)))
  rw [oldBefore211, at211, literal, oldAfter875, gammaAfter875]
  exact numeric
theorem numeric876 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 211 p
  rw [at211] at beforeRange
  have afterRange := bonus_range 212 (HazardPattern.afterPattern 10000 p (.walk 212))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) ∧ bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) ≤ 2 at afterRange
  rw [gammaAfter876] at afterRange
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
theorem local876 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 212 (HazardPattern.afterPattern 10000 p (.walk 212)) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 212) + NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 212))) + bonus 212 (HazardPattern.afterPattern 10000 p (.walk 212)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 212) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) < bonus 211 p at decreasing
  rw [gammaAfter876, at211] at decreasing
  have numeric := numeric876 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212))
  rw [oldBefore211, at211, literal, oldAfter876, gammaAfter876]
  exact numeric
theorem numeric877 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 211 p
  rw [at211] at beforeRange
  have afterRange := bonus_range 212 (HazardPattern.afterPattern 10000 p (.push 212 (.stay 213)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 212 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 212 (.stay 213))) ∧ bonus (HazardPattern.nextHero (.push 212 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 212 (.stay 213))) ≤ 2 at afterRange
  rw [gammaAfter877] at afterRange
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
theorem local877 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 212 (HazardPattern.afterPattern 10000 p (.push 212 (.stay 213))) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 212 (.stay 213)) + NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 212 (.stay 213)))) + bonus 212 (HazardPattern.afterPattern 10000 p (.push 212 (.stay 213))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 212 (.stay 213)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 212 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 212 (.stay 213))) < bonus 211 p at decreasing
  rw [gammaAfter877, at211] at decreasing
  have numeric := numeric877 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 212 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 212 (.stay 213)))
  rw [oldBefore211, at211, literal, oldAfter877, gammaAfter877]
  exact numeric
theorem numeric878 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 211 p
  rw [at211] at beforeRange
  have afterRange := bonus_range 210 (HazardPattern.afterPattern 10000 p (.walk 210))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210)) ∧ bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210)) ≤ 2 at afterRange
  rw [gammaAfter878] at afterRange
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
theorem local878 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 210 (HazardPattern.afterPattern 10000 p (.walk 210)) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 210) + NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 210))) + bonus 210 (HazardPattern.afterPattern 10000 p (.walk 210)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 210) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210)) < bonus 211 p at decreasing
  rw [gammaAfter878, at211] at decreasing
  have numeric := numeric878 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210))
  rw [oldBefore211, at211, literal, oldAfter878, gammaAfter878]
  exact numeric
theorem numeric879 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 211 p
  rw [at211] at beforeRange
  have afterRange := bonus_range 190 (HazardPattern.afterPattern 10000 p (.walk 190))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ∧ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ≤ 2 at afterRange
  rw [gammaAfter879] at afterRange
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
theorem local879 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 190) + NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 190))) + bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 190) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 211 p at decreasing
  rw [gammaAfter879, at211] at decreasing
  have numeric := numeric879 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190))
  rw [oldBefore211, at211, literal, oldAfter879, gammaAfter879]
  exact numeric
theorem numeric880 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 211 p
  rw [at211] at beforeRange
  have afterRange := bonus_range 188 (HazardPattern.afterPattern 10000 p (.walk 188))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) ∧ bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) ≤ 2 at afterRange
  rw [gammaAfter880] at afterRange
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
theorem local880 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 188 (HazardPattern.afterPattern 10000 p (.walk 188)) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 188) + NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 188))) + bonus 188 (HazardPattern.afterPattern 10000 p (.walk 188)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 188) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) < bonus 211 p at decreasing
  rw [gammaAfter880, at211] at decreasing
  have numeric := numeric880 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188))
  rw [oldBefore211, at211, literal, oldAfter880, gammaAfter880]
  exact numeric
theorem numeric881 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 212 p
  rw [at212] at beforeRange
  have afterRange := bonus_range 190 (HazardPattern.afterPattern 10000 p (.walk 190))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ∧ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ≤ 2 at afterRange
  rw [gammaAfter881] at afterRange
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
theorem local881 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 190) + NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 190))) + bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 190) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 212 p at decreasing
  rw [gammaAfter881, at212] at decreasing
  have numeric := numeric881 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190))
  rw [oldBefore212, at212, literal, oldAfter881, gammaAfter881]
  exact numeric
theorem numeric882 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 212 p
  rw [at212] at beforeRange
  have afterRange := bonus_range 190 (HazardPattern.afterPattern 10000 p (.push 190 (.stay 168)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 190 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 168))) ∧ bonus (HazardPattern.nextHero (.push 190 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 168))) ≤ 2 at afterRange
  rw [gammaAfter882] at afterRange
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
theorem local882 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 190 (HazardPattern.afterPattern 10000 p (.push 190 (.stay 168))) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 190 (.stay 168)) + NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 190 (.stay 168)))) + bonus 190 (HazardPattern.afterPattern 10000 p (.push 190 (.stay 168))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 190 (.stay 168)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 190 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 168))) < bonus 212 p at decreasing
  rw [gammaAfter882, at212] at decreasing
  have numeric := numeric882 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 190 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 168)))
  rw [oldBefore212, at212, literal, oldAfter882, gammaAfter882]
  exact numeric
theorem numeric883 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 212 p
  rw [at212] at beforeRange
  have afterRange := bonus_range 213 (HazardPattern.afterPattern 10000 p (.walk 213))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) ∧ bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) ≤ 2 at afterRange
  rw [gammaAfter883] at afterRange
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
theorem local883 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 213 (HazardPattern.afterPattern 10000 p (.walk 213)) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 213) + NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 213))) + bonus 213 (HazardPattern.afterPattern 10000 p (.walk 213)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 213) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) < bonus 212 p at decreasing
  rw [gammaAfter883, at212] at decreasing
  have numeric := numeric883 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213))
  rw [oldBefore212, at212, literal, oldAfter883, gammaAfter883]
  exact numeric
theorem numeric884 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 212 p
  rw [at212] at beforeRange
  have afterRange := bonus_range 213 (HazardPattern.afterPattern 10000 p (.push 213 (.stay 214)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 213 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 213 (.stay 214))) ∧ bonus (HazardPattern.nextHero (.push 213 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 213 (.stay 214))) ≤ 2 at afterRange
  rw [gammaAfter884] at afterRange
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
theorem local884 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 213 (HazardPattern.afterPattern 10000 p (.push 213 (.stay 214))) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 213 (.stay 214)) + NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 213 (.stay 214)))) + bonus 213 (HazardPattern.afterPattern 10000 p (.push 213 (.stay 214))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 213 (.stay 214)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 213 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 213 (.stay 214))) < bonus 212 p at decreasing
  rw [gammaAfter884, at212] at decreasing
  have numeric := numeric884 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 213 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 213 (.stay 214)))
  rw [oldBefore212, at212, literal, oldAfter884, gammaAfter884]
  exact numeric
theorem numeric885 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 212 p
  rw [at212] at beforeRange
  have afterRange := bonus_range 211 (HazardPattern.afterPattern 10000 p (.walk 211))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) ∧ bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) ≤ 2 at afterRange
  rw [gammaAfter885] at afterRange
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
theorem local885 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 211 (HazardPattern.afterPattern 10000 p (.walk 211)) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 211) + NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 211))) + bonus 211 (HazardPattern.afterPattern 10000 p (.walk 211)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 211) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) < bonus 212 p at decreasing
  rw [gammaAfter885, at212] at decreasing
  have numeric := numeric885 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211))
  rw [oldBefore212, at212, literal, oldAfter885, gammaAfter885]
  exact numeric
theorem numeric886 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 212 p
  rw [at212] at beforeRange
  have afterRange := bonus_range 211 (HazardPattern.afterPattern 10000 p (.push 211 (.stay 210)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 211 (.stay 210))) (HazardPattern.afterPattern 10000 p (.push 211 (.stay 210))) ∧ bonus (HazardPattern.nextHero (.push 211 (.stay 210))) (HazardPattern.afterPattern 10000 p (.push 211 (.stay 210))) ≤ 2 at afterRange
  rw [gammaAfter886] at afterRange
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
theorem local886 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 211 (HazardPattern.afterPattern 10000 p (.push 211 (.stay 210))) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 211 (.stay 210)) + NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 211 (.stay 210)))) + bonus 211 (HazardPattern.afterPattern 10000 p (.push 211 (.stay 210))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 211 (.stay 210)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 211 (.stay 210))) (HazardPattern.afterPattern 10000 p (.push 211 (.stay 210))) < bonus 212 p at decreasing
  rw [gammaAfter886, at212] at decreasing
  have numeric := numeric886 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 211 (.stay 210))) (HazardPattern.afterPattern 10000 p (.push 211 (.stay 210)))
  rw [oldBefore212, at212, literal, oldAfter886, gammaAfter886]
  exact numeric
theorem numeric887 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 212 p
  rw [at212] at beforeRange
  have afterRange := bonus_range 191 (HazardPattern.afterPattern 10000 p (.walk 191))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ∧ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ≤ 2 at afterRange
  rw [gammaAfter887] at afterRange
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
theorem local887 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 191) + NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 191))) + bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 191) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 212 p at decreasing
  rw [gammaAfter887, at212] at decreasing
  have numeric := numeric887 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191))
  rw [oldBefore212, at212, literal, oldAfter887, gammaAfter887]
  exact numeric
theorem numeric888 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 212 p
  rw [at212] at beforeRange
  have afterRange := bonus_range 189 (HazardPattern.afterPattern 10000 p (.walk 189))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ∧ bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) ≤ 2 at afterRange
  rw [gammaAfter888] at afterRange
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
theorem local888 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 189) + NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 189))) + bonus 189 (HazardPattern.afterPattern 10000 p (.walk 189)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 189) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) < bonus 212 p at decreasing
  rw [gammaAfter888, at212] at decreasing
  have numeric := numeric888 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189))
  rw [oldBefore212, at212, literal, oldAfter888, gammaAfter888]
  exact numeric
theorem numeric889 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 213 p
  rw [at213] at beforeRange
  have afterRange := bonus_range 191 (HazardPattern.afterPattern 10000 p (.walk 191))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ∧ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ≤ 2 at afterRange
  rw [gammaAfter889] at afterRange
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
theorem local889 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 213 p) :
    NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 213 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 191) + NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 191))) + bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 191) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 213 p at decreasing
  rw [gammaAfter889, at213] at decreasing
  have numeric := numeric889 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191))
  rw [oldBefore213, at213, literal, oldAfter889, gammaAfter889]
  exact numeric
theorem numeric890 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 213 p
  rw [at213] at beforeRange
  have afterRange := bonus_range 191 (HazardPattern.afterPattern 10000 p (.push 191 (.stay 169)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 191 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 169))) ∧ bonus (HazardPattern.nextHero (.push 191 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 169))) ≤ 2 at afterRange
  rw [gammaAfter890] at afterRange
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
theorem local890 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 191 (HazardPattern.afterPattern 10000 p (.push 191 (.stay 169))) < bonus 213 p) :
    NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 213 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 191 (.stay 169)) + NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 191 (.stay 169)))) + bonus 191 (HazardPattern.afterPattern 10000 p (.push 191 (.stay 169))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 191 (.stay 169)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 191 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 169))) < bonus 213 p at decreasing
  rw [gammaAfter890, at213] at decreasing
  have numeric := numeric890 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 191 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 169)))
  rw [oldBefore213, at213, literal, oldAfter890, gammaAfter890]
  exact numeric
theorem numeric891 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 213 p
  rw [at213] at beforeRange
  have afterRange := bonus_range 214 (HazardPattern.afterPattern 10000 p (.walk 214))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) ∧ bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) ≤ 2 at afterRange
  rw [gammaAfter891] at afterRange
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
theorem local891 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 214 (HazardPattern.afterPattern 10000 p (.walk 214)) < bonus 213 p) :
    NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 213 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 214) + NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 214))) + bonus 214 (HazardPattern.afterPattern 10000 p (.walk 214)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 214) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) < bonus 213 p at decreasing
  rw [gammaAfter891, at213] at decreasing
  have numeric := numeric891 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214))
  rw [oldBefore213, at213, literal, oldAfter891, gammaAfter891]
  exact numeric
theorem numeric892 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 213 p
  rw [at213] at beforeRange
  have afterRange := bonus_range 214 (HazardPattern.afterPattern 10000 p (.push 214 (.stay 215)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 214 (.stay 215))) (HazardPattern.afterPattern 10000 p (.push 214 (.stay 215))) ∧ bonus (HazardPattern.nextHero (.push 214 (.stay 215))) (HazardPattern.afterPattern 10000 p (.push 214 (.stay 215))) ≤ 2 at afterRange
  rw [gammaAfter892] at afterRange
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
theorem local892 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 214 (HazardPattern.afterPattern 10000 p (.push 214 (.stay 215))) < bonus 213 p) :
    NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 213 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 214 (.stay 215)) + NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 214 (.stay 215)))) + bonus 214 (HazardPattern.afterPattern 10000 p (.push 214 (.stay 215))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 214 (.stay 215)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 214 (.stay 215))) (HazardPattern.afterPattern 10000 p (.push 214 (.stay 215))) < bonus 213 p at decreasing
  rw [gammaAfter892, at213] at decreasing
  have numeric := numeric892 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 214 (.stay 215))) (HazardPattern.afterPattern 10000 p (.push 214 (.stay 215)))
  rw [oldBefore213, at213, literal, oldAfter892, gammaAfter892]
  exact numeric
theorem numeric893 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 213 p
  rw [at213] at beforeRange
  have afterRange := bonus_range 212 (HazardPattern.afterPattern 10000 p (.walk 212))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) ∧ bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) ≤ 2 at afterRange
  rw [gammaAfter893] at afterRange
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
theorem local893 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 212 (HazardPattern.afterPattern 10000 p (.walk 212)) < bonus 213 p) :
    NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 213 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 212) + NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 212))) + bonus 212 (HazardPattern.afterPattern 10000 p (.walk 212)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 212) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) < bonus 213 p at decreasing
  rw [gammaAfter893, at213] at decreasing
  have numeric := numeric893 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212))
  rw [oldBefore213, at213, literal, oldAfter893, gammaAfter893]
  exact numeric
theorem numeric894 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 213 p
  rw [at213] at beforeRange
  have afterRange := bonus_range 212 (HazardPattern.afterPattern 10000 p (.push 212 (.stay 211)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 212 (.stay 211))) (HazardPattern.afterPattern 10000 p (.push 212 (.stay 211))) ∧ bonus (HazardPattern.nextHero (.push 212 (.stay 211))) (HazardPattern.afterPattern 10000 p (.push 212 (.stay 211))) ≤ 2 at afterRange
  rw [gammaAfter894] at afterRange
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
theorem local894 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 212 (HazardPattern.afterPattern 10000 p (.push 212 (.stay 211))) < bonus 213 p) :
    NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 213 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 212 (.stay 211)) + NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 212 (.stay 211)))) + bonus 212 (HazardPattern.afterPattern 10000 p (.push 212 (.stay 211))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 212 (.stay 211)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 212 (.stay 211))) (HazardPattern.afterPattern 10000 p (.push 212 (.stay 211))) < bonus 213 p at decreasing
  rw [gammaAfter894, at213] at decreasing
  have numeric := numeric894 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 212 (.stay 211))) (HazardPattern.afterPattern 10000 p (.push 212 (.stay 211)))
  rw [oldBefore213, at213, literal, oldAfter894, gammaAfter894]
  exact numeric
theorem numeric895 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 213 p
  rw [at213] at beforeRange
  have afterRange := bonus_range 192 (HazardPattern.afterPattern 10000 p (.walk 192))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ∧ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ≤ 2 at afterRange
  rw [gammaAfter895] at afterRange
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
theorem local895 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 213 p) :
    NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 213 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 192) + NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 192))) + bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 192) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 213 p at decreasing
  rw [gammaAfter895, at213] at decreasing
  have numeric := numeric895 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192))
  rw [oldBefore213, at213, literal, oldAfter895, gammaAfter895]
  exact numeric
theorem numeric896 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 213 p
  rw [at213] at beforeRange
  have afterRange := bonus_range 190 (HazardPattern.afterPattern 10000 p (.walk 190))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ∧ bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) ≤ 2 at afterRange
  rw [gammaAfter896] at afterRange
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
theorem local896 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 213 p) :
    NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 213 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 190) + NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 190))) + bonus 190 (HazardPattern.afterPattern 10000 p (.walk 190)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 190) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) < bonus 213 p at decreasing
  rw [gammaAfter896, at213] at decreasing
  have numeric := numeric896 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190))
  rw [oldBefore213, at213, literal, oldAfter896, gammaAfter896]
  exact numeric
theorem numeric897 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 214 p
  rw [at214] at beforeRange
  have afterRange := bonus_range 192 (HazardPattern.afterPattern 10000 p (.walk 192))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ∧ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ≤ 2 at afterRange
  rw [gammaAfter897] at afterRange
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
theorem local897 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 214 p) :
    NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 214 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 192) + NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 192))) + bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 192) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 214 p at decreasing
  rw [gammaAfter897, at214] at decreasing
  have numeric := numeric897 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192))
  rw [oldBefore214, at214, literal, oldAfter897, gammaAfter897]
  exact numeric
theorem numeric898 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 214 p
  rw [at214] at beforeRange
  have afterRange := bonus_range 192 (HazardPattern.afterPattern 10000 p (.push 192 (.stay 170)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 192 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 170))) ∧ bonus (HazardPattern.nextHero (.push 192 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 170))) ≤ 2 at afterRange
  rw [gammaAfter898] at afterRange
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
theorem local898 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 192 (HazardPattern.afterPattern 10000 p (.push 192 (.stay 170))) < bonus 214 p) :
    NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 214 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 192 (.stay 170)) + NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 192 (.stay 170)))) + bonus 192 (HazardPattern.afterPattern 10000 p (.push 192 (.stay 170))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 192 (.stay 170)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 192 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 170))) < bonus 214 p at decreasing
  rw [gammaAfter898, at214] at decreasing
  have numeric := numeric898 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 192 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 170)))
  rw [oldBefore214, at214, literal, oldAfter898, gammaAfter898]
  exact numeric
theorem numeric899 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 214 p
  rw [at214] at beforeRange
  have afterRange := bonus_range 215 (HazardPattern.afterPattern 10000 p (.walk 215))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) ∧ bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) ≤ 2 at afterRange
  rw [gammaAfter899] at afterRange
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
theorem local899 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 215 (HazardPattern.afterPattern 10000 p (.walk 215)) < bonus 214 p) :
    NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 214 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 215) + NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 215))) + bonus 215 (HazardPattern.afterPattern 10000 p (.walk 215)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 215) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) < bonus 214 p at decreasing
  rw [gammaAfter899, at214] at decreasing
  have numeric := numeric899 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215))
  rw [oldBefore214, at214, literal, oldAfter899, gammaAfter899]
  exact numeric
theorem numeric900 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 214 p
  rw [at214] at beforeRange
  have afterRange := bonus_range 215 (HazardPattern.afterPattern 10000 p (.push 215 (.stay 216)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 215 (.stay 216))) (HazardPattern.afterPattern 10000 p (.push 215 (.stay 216))) ∧ bonus (HazardPattern.nextHero (.push 215 (.stay 216))) (HazardPattern.afterPattern 10000 p (.push 215 (.stay 216))) ≤ 2 at afterRange
  rw [gammaAfter900] at afterRange
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
theorem local900 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 215 (HazardPattern.afterPattern 10000 p (.push 215 (.stay 216))) < bonus 214 p) :
    NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 214 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 215 (.stay 216)) + NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 215 (.stay 216)))) + bonus 215 (HazardPattern.afterPattern 10000 p (.push 215 (.stay 216))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 215 (.stay 216)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 215 (.stay 216))) (HazardPattern.afterPattern 10000 p (.push 215 (.stay 216))) < bonus 214 p at decreasing
  rw [gammaAfter900, at214] at decreasing
  have numeric := numeric900 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 215 (.stay 216))) (HazardPattern.afterPattern 10000 p (.push 215 (.stay 216)))
  rw [oldBefore214, at214, literal, oldAfter900, gammaAfter900]
  exact numeric
theorem numeric901 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 214 p
  rw [at214] at beforeRange
  have afterRange := bonus_range 213 (HazardPattern.afterPattern 10000 p (.walk 213))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) ∧ bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) ≤ 2 at afterRange
  rw [gammaAfter901] at afterRange
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
theorem local901 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 213 (HazardPattern.afterPattern 10000 p (.walk 213)) < bonus 214 p) :
    NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 214 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 213) + NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 213))) + bonus 213 (HazardPattern.afterPattern 10000 p (.walk 213)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 213) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) < bonus 214 p at decreasing
  rw [gammaAfter901, at214] at decreasing
  have numeric := numeric901 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213))
  rw [oldBefore214, at214, literal, oldAfter901, gammaAfter901]
  exact numeric
theorem numeric902 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 214 p
  rw [at214] at beforeRange
  have afterRange := bonus_range 213 (HazardPattern.afterPattern 10000 p (.push 213 (.stay 212)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 213 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 213 (.stay 212))) ∧ bonus (HazardPattern.nextHero (.push 213 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 213 (.stay 212))) ≤ 2 at afterRange
  rw [gammaAfter902] at afterRange
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
theorem local902 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 213 (HazardPattern.afterPattern 10000 p (.push 213 (.stay 212))) < bonus 214 p) :
    NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 214 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 213 (.stay 212)) + NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 213 (.stay 212)))) + bonus 213 (HazardPattern.afterPattern 10000 p (.push 213 (.stay 212))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 213 (.stay 212)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 213 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 213 (.stay 212))) < bonus 214 p at decreasing
  rw [gammaAfter902, at214] at decreasing
  have numeric := numeric902 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 213 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 213 (.stay 212)))
  rw [oldBefore214, at214, literal, oldAfter902, gammaAfter902]
  exact numeric
theorem numeric903 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 214 p
  rw [at214] at beforeRange
  have afterRange := bonus_range 193 (HazardPattern.afterPattern 10000 p (.walk 193))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ∧ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ≤ 2 at afterRange
  rw [gammaAfter903] at afterRange
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
theorem local903 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 214 p) :
    NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 214 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 193) + NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 193))) + bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 193) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 214 p at decreasing
  rw [gammaAfter903, at214] at decreasing
  have numeric := numeric903 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193))
  rw [oldBefore214, at214, literal, oldAfter903, gammaAfter903]
  exact numeric
theorem numeric904 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 214 p
  rw [at214] at beforeRange
  have afterRange := bonus_range 191 (HazardPattern.afterPattern 10000 p (.walk 191))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ∧ bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) ≤ 2 at afterRange
  rw [gammaAfter904] at afterRange
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
theorem local904 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 214 p) :
    NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 214 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 191) + NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 191))) + bonus 191 (HazardPattern.afterPattern 10000 p (.walk 191)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 191) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) < bonus 214 p at decreasing
  rw [gammaAfter904, at214] at decreasing
  have numeric := numeric904 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191))
  rw [oldBefore214, at214, literal, oldAfter904, gammaAfter904]
  exact numeric
theorem numeric905 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 215 p
  rw [at215] at beforeRange
  have afterRange := bonus_range 193 (HazardPattern.afterPattern 10000 p (.walk 193))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ∧ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ≤ 2 at afterRange
  rw [gammaAfter905] at afterRange
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
theorem local905 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 215 p) :
    NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 215 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 193) + NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 193))) + bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 193) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 215 p at decreasing
  rw [gammaAfter905, at215] at decreasing
  have numeric := numeric905 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193))
  rw [oldBefore215, at215, literal, oldAfter905, gammaAfter905]
  exact numeric
theorem numeric906 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 215 p
  rw [at215] at beforeRange
  have afterRange := bonus_range 193 (HazardPattern.afterPattern 10000 p (.push 193 (.stay 171)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 193 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 171))) ∧ bonus (HazardPattern.nextHero (.push 193 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 171))) ≤ 2 at afterRange
  rw [gammaAfter906] at afterRange
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
theorem local906 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 193 (HazardPattern.afterPattern 10000 p (.push 193 (.stay 171))) < bonus 215 p) :
    NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 215 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 193 (.stay 171)) + NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 193 (.stay 171)))) + bonus 193 (HazardPattern.afterPattern 10000 p (.push 193 (.stay 171))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 193 (.stay 171)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 193 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 171))) < bonus 215 p at decreasing
  rw [gammaAfter906, at215] at decreasing
  have numeric := numeric906 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 193 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 171)))
  rw [oldBefore215, at215, literal, oldAfter906, gammaAfter906]
  exact numeric
theorem numeric907 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 215 p
  rw [at215] at beforeRange
  have afterRange := bonus_range 216 (HazardPattern.afterPattern 10000 p (.walk 216))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 216)) (HazardPattern.afterPattern 10000 p (.walk 216)) ∧ bonus (HazardPattern.nextHero (.walk 216)) (HazardPattern.afterPattern 10000 p (.walk 216)) ≤ 2 at afterRange
  rw [gammaAfter907] at afterRange
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
theorem local907 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 216 (HazardPattern.afterPattern 10000 p (.walk 216)) < bonus 215 p) :
    NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 215 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 216) + NetHack.Sokoban22Refined85.bonus 216 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 216))) + bonus 216 (HazardPattern.afterPattern 10000 p (.walk 216)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 216) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 216)) (HazardPattern.afterPattern 10000 p (.walk 216)) < bonus 215 p at decreasing
  rw [gammaAfter907, at215] at decreasing
  have numeric := numeric907 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 216)) (HazardPattern.afterPattern 10000 p (.walk 216))
  rw [oldBefore215, at215, literal, oldAfter907, gammaAfter907]
  exact numeric
theorem numeric908 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 215 p
  rw [at215] at beforeRange
  have afterRange := bonus_range 214 (HazardPattern.afterPattern 10000 p (.walk 214))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) ∧ bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) ≤ 2 at afterRange
  rw [gammaAfter908] at afterRange
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
theorem local908 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 214 (HazardPattern.afterPattern 10000 p (.walk 214)) < bonus 215 p) :
    NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 215 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 214) + NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 214))) + bonus 214 (HazardPattern.afterPattern 10000 p (.walk 214)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 214) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214)) < bonus 215 p at decreasing
  rw [gammaAfter908, at215] at decreasing
  have numeric := numeric908 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 214)) (HazardPattern.afterPattern 10000 p (.walk 214))
  rw [oldBefore215, at215, literal, oldAfter908, gammaAfter908]
  exact numeric
theorem numeric909 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 215 p
  rw [at215] at beforeRange
  have afterRange := bonus_range 214 (HazardPattern.afterPattern 10000 p (.push 214 (.stay 213)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 214 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 214 (.stay 213))) ∧ bonus (HazardPattern.nextHero (.push 214 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 214 (.stay 213))) ≤ 2 at afterRange
  rw [gammaAfter909] at afterRange
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
theorem local909 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 214 (HazardPattern.afterPattern 10000 p (.push 214 (.stay 213))) < bonus 215 p) :
    NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 215 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 214 (.stay 213)) + NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 214 (.stay 213)))) + bonus 214 (HazardPattern.afterPattern 10000 p (.push 214 (.stay 213))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 214 (.stay 213)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 214 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 214 (.stay 213))) < bonus 215 p at decreasing
  rw [gammaAfter909, at215] at decreasing
  have numeric := numeric909 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 214 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 214 (.stay 213)))
  rw [oldBefore215, at215, literal, oldAfter909, gammaAfter909]
  exact numeric
end NetHack.Soko22Hazard87
