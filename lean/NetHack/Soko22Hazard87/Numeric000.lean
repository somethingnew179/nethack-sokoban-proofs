import NetHack.Soko22Hazard87.NumericBase
import NetHack.Soko22Hazard87.AndIntroBlocks0011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric0 (p : Pattern) (guard : d51640 p = 1) (decreasing : d2518 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 25 p
  rw [at25] at beforeRange
  have afterRange := bonus_range 47 (HazardPattern.afterPattern 10000 p (.walk 47))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) ∧ bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) ≤ 2 at afterRange
  rw [gammaAfter0] at afterRange
  have possibilities : (d2518 p = 1 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro0 p guard beforeEq
    have complete := andIntro321 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro322 p guard beforeEq
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro322 p guard beforeEq
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local0 (p : Pattern) (guard : d51640 p = 1)
    (decreasing : bonus 47 (HazardPattern.afterPattern 10000 p (.walk 47)) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 47) + NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 47))) + bonus 47 (HazardPattern.afterPattern 10000 p (.walk 47)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 47) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) < bonus 25 p at decreasing
  rw [gammaAfter0, at25] at decreasing
  have numeric := numeric0 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47))
  rw [oldBefore25, at25, literal, oldAfter0, gammaAfter0]
  exact numeric
theorem numeric1 (p : Pattern) (guard : d53870 p = 1) (decreasing : d54026 p < d2518 p) :
    d47866 p + d2518 p ≤ (1 : Int) + d47866 p + d54026 p := by
  have beforeRange := bonus_range 25 p
  rw [at25] at beforeRange
  have afterRange := bonus_range 47 (HazardPattern.afterPattern 10000 p (.push 47 (.stay 69)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 47 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 69))) ∧ bonus (HazardPattern.nextHero (.push 47 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 69))) ≤ 2 at afterRange
  rw [gammaAfter1] at afterRange
  have possibilities : (d2518 p = 1 ∧ d54026 p = 0) ∨ (d2518 p = 2 ∧ d54026 p = 0) ∨ (d2518 p = 2 ∧ d54026 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1122 p pair.2
    have combined := andIntro422 p beforeEq guard
    have complete := andIntro423 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1122 p pair.2
    have combined := andIntro425 p beforeEq guard
    have complete := andIntro423 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1123 p pair.2
    have combined := andIntro425 p beforeEq guard
    have complete := andIntro426 p combined afterEq
    have bound := compare2 p complete
    omega
theorem local1 (p : Pattern) (guard : d53870 p = 1)
    (decreasing : bonus 47 (HazardPattern.afterPattern 10000 p (.push 47 (.stay 69))) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 47 (.stay 69)) + NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 47 (.stay 69)))) + bonus 47 (HazardPattern.afterPattern 10000 p (.push 47 (.stay 69))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 47 (.stay 69)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 47 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 69))) < bonus 25 p at decreasing
  rw [gammaAfter1, at25] at decreasing
  have numeric := numeric1 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 47 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 69)))
  rw [oldBefore25, at25, literal, oldAfter1, gammaAfter1]
  exact numeric
theorem numeric2 (p : Pattern) (guard : d54186 p = 1) (decreasing : d2782 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d48080 p + d2782 p := by
  have beforeRange := bonus_range 25 p
  rw [at25] at beforeRange
  have afterRange := bonus_range 48 (HazardPattern.afterPattern 10000 p (.walk 48))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ∧ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ≤ 2 at afterRange
  rw [gammaAfter2] at afterRange
  have possibilities : (d2518 p = 1 ∧ d2782 p = 0) ∨ (d2518 p = 2 ∧ d2782 p = 0) ∨ (d2518 p = 2 ∧ d2782 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro448 p beforeEq guard
    have complete := andIntro470 p afterEq combined
    have bound := compare3 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro491 p beforeEq guard
    have complete := andIntro512 p afterEq combined
    have bound := compare4 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1166 p pair.2
    have combined := andIntro491 p beforeEq guard
    have complete := andIntro533 p afterEq combined
    have bound := compare3 p complete
    omega
theorem local2 (p : Pattern) (guard : d54186 p = 1)
    (decreasing : bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 48) + NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 48))) + bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 48) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 25 p at decreasing
  rw [gammaAfter2, at25] at decreasing
  have numeric := numeric2 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48))
  rw [oldBefore25, at25, literal, oldAfter2, gammaAfter2]
  exact numeric
theorem numeric3 (p : Pattern) (guard : d54513 p = 1) (decreasing : d2518 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 25 p
  rw [at25] at beforeRange
  have afterRange := bonus_range 46 (HazardPattern.afterPattern 10000 p (.walk 46))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) ∧ bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) ≤ 2 at afterRange
  rw [gammaAfter3] at afterRange
  have possibilities : (d2518 p = 1 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro534 p beforeEq guard
    have complete := andIntro321 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro535 p beforeEq guard
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro535 p beforeEq guard
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local3 (p : Pattern) (guard : d54513 p = 1)
    (decreasing : bonus 46 (HazardPattern.afterPattern 10000 p (.walk 46)) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 46) + NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 46))) + bonus 46 (HazardPattern.afterPattern 10000 p (.walk 46)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 46) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) < bonus 25 p at decreasing
  rw [gammaAfter3, at25] at decreasing
  have numeric := numeric3 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46))
  rw [oldBefore25, at25, literal, oldAfter3, gammaAfter3]
  exact numeric
theorem numeric4 (p : Pattern) (guard : d54518 p = 1) (decreasing : d2895 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d48083 p + d2895 p := by
  have beforeRange := bonus_range 27 p
  rw [at27] at beforeRange
  have afterRange := bonus_range 49 (HazardPattern.afterPattern 10000 p (.walk 49))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) ∧ bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) ≤ 2 at afterRange
  rw [gammaAfter4] at afterRange
  have possibilities : (d2671 p = 1 ∧ d2895 p = 0) ∨ (d2671 p = 2 ∧ d2895 p = 0) ∨ (d2671 p = 2 ∧ d2895 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1209 p pair.2
    have combined := andIntro556 p guard beforeEq
    have complete := andIntro578 p afterEq combined
    have bound := compare5 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1209 p pair.2
    have combined := andIntro579 p guard beforeEq
    have complete := andIntro600 p afterEq combined
    have bound := compare6 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1258 p pair.2
    have combined := andIntro579 p guard beforeEq
    have complete := andIntro621 p afterEq combined
    have bound := compare5 p complete
    omega
theorem local4 (p : Pattern) (guard : d54518 p = 1)
    (decreasing : bonus 49 (HazardPattern.afterPattern 10000 p (.walk 49)) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 49) + NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 49))) + bonus 49 (HazardPattern.afterPattern 10000 p (.walk 49)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 49) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) < bonus 27 p at decreasing
  rw [gammaAfter4, at27] at decreasing
  have numeric := numeric4 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49))
  rw [oldBefore27, at27, literal, oldAfter4, gammaAfter4]
  exact numeric
theorem numeric5 (p : Pattern) (guard : d54981 p = 1) (decreasing : d55164 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47700 p + d55164 p := by
  have beforeRange := bonus_range 27 p
  rw [at27] at beforeRange
  have afterRange := bonus_range 49 (HazardPattern.afterPattern 10000 p (.push 49 (.stay 71)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 49 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 71))) ∧ bonus (HazardPattern.nextHero (.push 49 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 71))) ≤ 2 at afterRange
  rw [gammaAfter5] at afterRange
  have possibilities : (d2671 p = 1 ∧ d55164 p = 0) ∨ (d2671 p = 2 ∧ d55164 p = 0) ∨ (d2671 p = 2 ∧ d55164 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1320 p pair.2
    have combined := andIntro643 p beforeEq guard
    have complete := andIntro671 p afterEq combined
    have bound := compare7 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1320 p pair.2
    have combined := andIntro692 p beforeEq guard
    have complete := andIntro693 p combined afterEq
    have bound := compare8 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1355 p pair.2
    have combined := andIntro692 p beforeEq guard
    have complete := andIntro694 p combined afterEq
    have bound := compare7 p complete
    omega
theorem local5 (p : Pattern) (guard : d54981 p = 1)
    (decreasing : bonus 49 (HazardPattern.afterPattern 10000 p (.push 49 (.stay 71))) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 49 (.stay 71)) + NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 49 (.stay 71)))) + bonus 49 (HazardPattern.afterPattern 10000 p (.push 49 (.stay 71))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 49 (.stay 71)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 49 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 71))) < bonus 27 p at decreasing
  rw [gammaAfter5, at27] at decreasing
  have numeric := numeric5 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 49 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 71)))
  rw [oldBefore27, at27, literal, oldAfter5, gammaAfter5]
  exact numeric
theorem numeric6 (p : Pattern) (guard : d55597 p = 1) (decreasing : d2671 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 27 p
  rw [at27] at beforeRange
  have afterRange := bonus_range 28 (HazardPattern.afterPattern 10000 p (.walk 28))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) ∧ bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) ≤ 2 at afterRange
  rw [gammaAfter6] at afterRange
  have possibilities : (d2671 p = 1 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro695 p beforeEq guard
    have complete := andIntro722 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro723 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro723 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare9 p complete
    omega
theorem local6 (p : Pattern) (guard : d55597 p = 1)
    (decreasing : bonus 28 (HazardPattern.afterPattern 10000 p (.walk 28)) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 28) + NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 28))) + bonus 28 (HazardPattern.afterPattern 10000 p (.walk 28)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 28) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) < bonus 27 p at decreasing
  rw [gammaAfter6, at27] at decreasing
  have numeric := numeric6 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28))
  rw [oldBefore27, at27, literal, oldAfter6, gammaAfter6]
  exact numeric
theorem numeric7 (p : Pattern) (guard : d55749 p = 1) (decreasing : d0 p < d2671 p) :
    d47911 p + d2671 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 27 p
  rw [at27] at beforeRange
  have afterRange := bonus_range 28 (HazardPattern.afterPattern 10000 p (.push 28 (.stay 29)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 28 (.stay 29))) (HazardPattern.afterPattern 10000 p (.push 28 (.stay 29))) ∧ bonus (HazardPattern.nextHero (.push 28 (.stay 29))) (HazardPattern.afterPattern 10000 p (.push 28 (.stay 29))) ≤ 2 at afterRange
  rw [gammaAfter7] at afterRange
  have possibilities : (d2671 p = 1 ∧ d0 p = 0) ∨ (d2671 p = 2 ∧ d0 p = 0) ∨ (d2671 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro766 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro768 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro768 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local7 (p : Pattern) (guard : d55749 p = 1)
    (decreasing : bonus 28 (HazardPattern.afterPattern 10000 p (.push 28 (.stay 29))) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 28 (.stay 29)) + NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 28 (.stay 29)))) + bonus 28 (HazardPattern.afterPattern 10000 p (.push 28 (.stay 29))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 28 (.stay 29)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 28 (.stay 29))) (HazardPattern.afterPattern 10000 p (.push 28 (.stay 29))) < bonus 27 p at decreasing
  rw [gammaAfter7, at27] at decreasing
  have numeric := numeric7 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 28 (.stay 29))) (HazardPattern.afterPattern 10000 p (.push 28 (.stay 29)))
  rw [oldBefore27, at27, literal, oldAfter7, gammaAfter7]
  exact numeric
theorem numeric8 (p : Pattern) (guard : d55757 p = 1) (decreasing : d3015 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d3015 p := by
  have beforeRange := bonus_range 27 p
  rw [at27] at beforeRange
  have afterRange := bonus_range 50 (HazardPattern.afterPattern 10000 p (.walk 50))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ∧ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ≤ 2 at afterRange
  rw [gammaAfter8] at afterRange
  have possibilities : (d2671 p = 1 ∧ d3015 p = 0) ∨ (d2671 p = 2 ∧ d3015 p = 0) ∨ (d2671 p = 2 ∧ d3015 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro791 p beforeEq guard
    have complete := andIntro812 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro833 p beforeEq guard
    have complete := andIntro834 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1406 p pair.2
    have combined := andIntro833 p beforeEq guard
    have complete := andIntro835 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local8 (p : Pattern) (guard : d55757 p = 1)
    (decreasing : bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 50) + NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 50))) + bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 50) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 27 p at decreasing
  rw [gammaAfter8, at27] at decreasing
  have numeric := numeric8 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50))
  rw [oldBefore27, at27, literal, oldAfter8, gammaAfter8]
  exact numeric
theorem numeric9 (p : Pattern) (guard : d55879 p = 1) (decreasing : d2782 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d48080 p + d2782 p := by
  have beforeRange := bonus_range 27 p
  rw [at27] at beforeRange
  have afterRange := bonus_range 48 (HazardPattern.afterPattern 10000 p (.walk 48))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ∧ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ≤ 2 at afterRange
  rw [gammaAfter9] at afterRange
  have possibilities : (d2671 p = 1 ∧ d2782 p = 0) ∨ (d2671 p = 2 ∧ d2782 p = 0) ∨ (d2671 p = 2 ∧ d2782 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro856 p beforeEq guard
    have complete := andIntro878 p afterEq combined
    have bound := compare12 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro879 p beforeEq guard
    have complete := andIntro900 p afterEq combined
    have bound := compare13 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1166 p pair.2
    have combined := andIntro879 p beforeEq guard
    have complete := andIntro921 p afterEq combined
    have bound := compare12 p complete
    omega
theorem local9 (p : Pattern) (guard : d55879 p = 1)
    (decreasing : bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 48) + NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 48))) + bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 48) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 27 p at decreasing
  rw [gammaAfter9, at27] at decreasing
  have numeric := numeric9 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48))
  rw [oldBefore27, at27, literal, oldAfter9, gammaAfter9]
  exact numeric
theorem numeric10 (p : Pattern) (guard : d55880 p = 1) (decreasing : d3015 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d3015 p := by
  have beforeRange := bonus_range 28 p
  rw [at28] at beforeRange
  have afterRange := bonus_range 50 (HazardPattern.afterPattern 10000 p (.walk 50))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ∧ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ≤ 2 at afterRange
  rw [gammaAfter10] at afterRange
  have possibilities : (d2671 p = 1 ∧ d3015 p = 0) ∨ (d2671 p = 2 ∧ d3015 p = 0) ∨ (d2671 p = 2 ∧ d3015 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro922 p beforeEq guard
    have complete := andIntro812 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro923 p beforeEq guard
    have complete := andIntro834 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1406 p pair.2
    have combined := andIntro923 p beforeEq guard
    have complete := andIntro835 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local10 (p : Pattern) (guard : d55880 p = 1)
    (decreasing : bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 50) + NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 50))) + bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 50) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 28 p at decreasing
  rw [gammaAfter10, at28] at decreasing
  have numeric := numeric10 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50))
  rw [oldBefore28, at28, literal, oldAfter10, gammaAfter10]
  exact numeric
theorem numeric11 (p : Pattern) (guard : d55881 p = 1) (decreasing : d2671 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 28 p
  rw [at28] at beforeRange
  have afterRange := bonus_range 29 (HazardPattern.afterPattern 10000 p (.walk 29))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) ∧ bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) ≤ 2 at afterRange
  rw [gammaAfter11] at afterRange
  have possibilities : (d2671 p = 1 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro924 p beforeEq guard
    have complete := andIntro722 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro925 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro925 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare9 p complete
    omega
theorem local11 (p : Pattern) (guard : d55881 p = 1)
    (decreasing : bonus 29 (HazardPattern.afterPattern 10000 p (.walk 29)) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 29) + NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 29))) + bonus 29 (HazardPattern.afterPattern 10000 p (.walk 29)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 29) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) < bonus 28 p at decreasing
  rw [gammaAfter11, at28] at decreasing
  have numeric := numeric11 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29))
  rw [oldBefore28, at28, literal, oldAfter11, gammaAfter11]
  exact numeric
theorem numeric12 (p : Pattern) (guard : d55886 p = 1) (decreasing : d0 p < d2671 p) :
    d47911 p + d2671 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 28 p
  rw [at28] at beforeRange
  have afterRange := bonus_range 29 (HazardPattern.afterPattern 10000 p (.push 29 (.stay 30)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 29 (.stay 30))) (HazardPattern.afterPattern 10000 p (.push 29 (.stay 30))) ∧ bonus (HazardPattern.nextHero (.push 29 (.stay 30))) (HazardPattern.afterPattern 10000 p (.push 29 (.stay 30))) ≤ 2 at afterRange
  rw [gammaAfter12] at afterRange
  have possibilities : (d2671 p = 1 ∧ d0 p = 0) ∨ (d2671 p = 2 ∧ d0 p = 0) ∨ (d2671 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro926 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro927 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro927 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local12 (p : Pattern) (guard : d55886 p = 1)
    (decreasing : bonus 29 (HazardPattern.afterPattern 10000 p (.push 29 (.stay 30))) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 29 (.stay 30)) + NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 29 (.stay 30)))) + bonus 29 (HazardPattern.afterPattern 10000 p (.push 29 (.stay 30))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 29 (.stay 30)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 29 (.stay 30))) (HazardPattern.afterPattern 10000 p (.push 29 (.stay 30))) < bonus 28 p at decreasing
  rw [gammaAfter12, at28] at decreasing
  have numeric := numeric12 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 29 (.stay 30))) (HazardPattern.afterPattern 10000 p (.push 29 (.stay 30)))
  rw [oldBefore28, at28, literal, oldAfter12, gammaAfter12]
  exact numeric
theorem numeric13 (p : Pattern) (guard : d55597 p = 1) (decreasing : d2671 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 28 p
  rw [at28] at beforeRange
  have afterRange := bonus_range 27 (HazardPattern.afterPattern 10000 p (.walk 27))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27)) ∧ bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27)) ≤ 2 at afterRange
  rw [gammaAfter13] at afterRange
  have possibilities : (d2671 p = 1 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro695 p beforeEq guard
    have complete := andIntro722 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro723 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro723 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare9 p complete
    omega
theorem local13 (p : Pattern) (guard : d55597 p = 1)
    (decreasing : bonus 27 (HazardPattern.afterPattern 10000 p (.walk 27)) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 27) + NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 27))) + bonus 27 (HazardPattern.afterPattern 10000 p (.walk 27)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 27) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27)) < bonus 28 p at decreasing
  rw [gammaAfter13, at28] at decreasing
  have numeric := numeric13 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27))
  rw [oldBefore28, at28, literal, oldAfter13, gammaAfter13]
  exact numeric
theorem numeric14 (p : Pattern) (guard : d55894 p = 1) (decreasing : d3142 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d3142 p := by
  have beforeRange := bonus_range 28 p
  rw [at28] at beforeRange
  have afterRange := bonus_range 51 (HazardPattern.afterPattern 10000 p (.walk 51))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ∧ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ≤ 2 at afterRange
  rw [gammaAfter14] at afterRange
  have possibilities : (d2671 p = 1 ∧ d3142 p = 0) ∨ (d2671 p = 2 ∧ d3142 p = 0) ∨ (d2671 p = 2 ∧ d3142 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro948 p beforeEq guard
    have complete := andIntro969 p afterEq combined
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro970 p beforeEq guard
    have complete := andIntro991 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1448 p pair.2
    have combined := andIntro970 p beforeEq guard
    have complete := andIntro1012 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local14 (p : Pattern) (guard : d55894 p = 1)
    (decreasing : bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 51) + NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 51))) + bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 51) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 28 p at decreasing
  rw [gammaAfter14, at28] at decreasing
  have numeric := numeric14 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51))
  rw [oldBefore28, at28, literal, oldAfter14, gammaAfter14]
  exact numeric
theorem numeric15 (p : Pattern) (guard : d56147 p = 1) (decreasing : d2895 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d48083 p + d2895 p := by
  have beforeRange := bonus_range 28 p
  rw [at28] at beforeRange
  have afterRange := bonus_range 49 (HazardPattern.afterPattern 10000 p (.walk 49))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) ∧ bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) ≤ 2 at afterRange
  rw [gammaAfter15] at afterRange
  have possibilities : (d2671 p = 1 ∧ d2895 p = 0) ∨ (d2671 p = 2 ∧ d2895 p = 0) ∨ (d2671 p = 2 ∧ d2895 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1209 p pair.2
    have combined := andIntro1013 p beforeEq guard
    have complete := andIntro578 p afterEq combined
    have bound := compare5 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1209 p pair.2
    have combined := andIntro1014 p beforeEq guard
    have complete := andIntro600 p afterEq combined
    have bound := compare6 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1258 p pair.2
    have combined := andIntro1014 p beforeEq guard
    have complete := andIntro621 p afterEq combined
    have bound := compare5 p complete
    omega
theorem local15 (p : Pattern) (guard : d56147 p = 1)
    (decreasing : bonus 49 (HazardPattern.afterPattern 10000 p (.walk 49)) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 49) + NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 49))) + bonus 49 (HazardPattern.afterPattern 10000 p (.walk 49)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 49) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) < bonus 28 p at decreasing
  rw [gammaAfter15, at28] at decreasing
  have numeric := numeric15 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49))
  rw [oldBefore28, at28, literal, oldAfter15, gammaAfter15]
  exact numeric
theorem numeric16 (p : Pattern) (guard : d56148 p = 1) (decreasing : d3142 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d3142 p := by
  have beforeRange := bonus_range 29 p
  rw [at29] at beforeRange
  have afterRange := bonus_range 51 (HazardPattern.afterPattern 10000 p (.walk 51))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ∧ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ≤ 2 at afterRange
  rw [gammaAfter16] at afterRange
  have possibilities : (d2671 p = 1 ∧ d3142 p = 0) ∨ (d2671 p = 2 ∧ d3142 p = 0) ∨ (d2671 p = 2 ∧ d3142 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro1015 p beforeEq guard
    have complete := andIntro969 p afterEq combined
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro1016 p beforeEq guard
    have complete := andIntro991 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1448 p pair.2
    have combined := andIntro1016 p beforeEq guard
    have complete := andIntro1012 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local16 (p : Pattern) (guard : d56148 p = 1)
    (decreasing : bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 51) + NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 51))) + bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 51) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 29 p at decreasing
  rw [gammaAfter16, at29] at decreasing
  have numeric := numeric16 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51))
  rw [oldBefore29, at29, literal, oldAfter16, gammaAfter16]
  exact numeric
theorem numeric17 (p : Pattern) (guard : d56153 p = 1) (decreasing : d56380 p < d2671 p) :
    d47911 p + d2671 p ≤ (1 : Int) + d47911 p + d56380 p := by
  have beforeRange := bonus_range 29 p
  rw [at29] at beforeRange
  have afterRange := bonus_range 51 (HazardPattern.afterPattern 10000 p (.push 51 (.stay 73)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 51 (.stay 73))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 73))) ∧ bonus (HazardPattern.nextHero (.push 51 (.stay 73))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 73))) ≤ 2 at afterRange
  rw [gammaAfter17] at afterRange
  have possibilities : (d2671 p = 1 ∧ d56380 p = 0) ∨ (d2671 p = 2 ∧ d56380 p = 0) ∨ (d2671 p = 2 ∧ d56380 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1512 p pair.2
    have combined := andIntro1052 p beforeEq guard
    have complete := andIntro1053 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1512 p pair.2
    have combined := andIntro1074 p beforeEq guard
    have complete := andIntro1053 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1547 p pair.2
    have combined := andIntro1074 p beforeEq guard
    have complete := andIntro1075 p combined afterEq
    have bound := compare11 p complete
    omega
theorem local17 (p : Pattern) (guard : d56153 p = 1)
    (decreasing : bonus 51 (HazardPattern.afterPattern 10000 p (.push 51 (.stay 73))) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 51 (.stay 73)) + NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 51 (.stay 73)))) + bonus 51 (HazardPattern.afterPattern 10000 p (.push 51 (.stay 73))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 51 (.stay 73)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 51 (.stay 73))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 73))) < bonus 29 p at decreasing
  rw [gammaAfter17, at29] at decreasing
  have numeric := numeric17 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 51 (.stay 73))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 73)))
  rw [oldBefore29, at29, literal, oldAfter17, gammaAfter17]
  exact numeric
theorem numeric18 (p : Pattern) (guard : d56756 p = 1) (decreasing : d2671 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 29 p
  rw [at29] at beforeRange
  have afterRange := bonus_range 30 (HazardPattern.afterPattern 10000 p (.walk 30))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 30)) (HazardPattern.afterPattern 10000 p (.walk 30)) ∧ bonus (HazardPattern.nextHero (.walk 30)) (HazardPattern.afterPattern 10000 p (.walk 30)) ≤ 2 at afterRange
  rw [gammaAfter18] at afterRange
  have possibilities : (d2671 p = 1 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1076 p beforeEq guard
    have complete := andIntro722 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1077 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro1077 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare9 p complete
    omega
theorem local18 (p : Pattern) (guard : d56756 p = 1)
    (decreasing : bonus 30 (HazardPattern.afterPattern 10000 p (.walk 30)) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 30) + NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 30))) + bonus 30 (HazardPattern.afterPattern 10000 p (.walk 30)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 30) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 30)) (HazardPattern.afterPattern 10000 p (.walk 30)) < bonus 29 p at decreasing
  rw [gammaAfter18, at29] at decreasing
  have numeric := numeric18 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 30)) (HazardPattern.afterPattern 10000 p (.walk 30))
  rw [oldBefore29, at29, literal, oldAfter18, gammaAfter18]
  exact numeric
theorem numeric19 (p : Pattern) (guard : d55881 p = 1) (decreasing : d2671 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 29 p
  rw [at29] at beforeRange
  have afterRange := bonus_range 28 (HazardPattern.afterPattern 10000 p (.walk 28))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) ∧ bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) ≤ 2 at afterRange
  rw [gammaAfter19] at afterRange
  have possibilities : (d2671 p = 1 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro924 p beforeEq guard
    have complete := andIntro722 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro925 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro925 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare9 p complete
    omega
theorem local19 (p : Pattern) (guard : d55881 p = 1)
    (decreasing : bonus 28 (HazardPattern.afterPattern 10000 p (.walk 28)) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 28) + NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 28))) + bonus 28 (HazardPattern.afterPattern 10000 p (.walk 28)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 28) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) < bonus 29 p at decreasing
  rw [gammaAfter19, at29] at decreasing
  have numeric := numeric19 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28))
  rw [oldBefore29, at29, literal, oldAfter19, gammaAfter19]
  exact numeric
theorem numeric20 (p : Pattern) (guard : d55749 p = 1) (decreasing : d0 p < d2671 p) :
    d47911 p + d2671 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 29 p
  rw [at29] at beforeRange
  have afterRange := bonus_range 28 (HazardPattern.afterPattern 10000 p (.push 28 (.stay 27)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 28 (.stay 27))) (HazardPattern.afterPattern 10000 p (.push 28 (.stay 27))) ∧ bonus (HazardPattern.nextHero (.push 28 (.stay 27))) (HazardPattern.afterPattern 10000 p (.push 28 (.stay 27))) ≤ 2 at afterRange
  rw [gammaAfter20] at afterRange
  have possibilities : (d2671 p = 1 ∧ d0 p = 0) ∨ (d2671 p = 2 ∧ d0 p = 0) ∨ (d2671 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro766 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro768 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro768 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local20 (p : Pattern) (guard : d55749 p = 1)
    (decreasing : bonus 28 (HazardPattern.afterPattern 10000 p (.push 28 (.stay 27))) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 28 (.stay 27)) + NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 28 (.stay 27)))) + bonus 28 (HazardPattern.afterPattern 10000 p (.push 28 (.stay 27))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 28 (.stay 27)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 28 (.stay 27))) (HazardPattern.afterPattern 10000 p (.push 28 (.stay 27))) < bonus 29 p at decreasing
  rw [gammaAfter20, at29] at decreasing
  have numeric := numeric20 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 28 (.stay 27))) (HazardPattern.afterPattern 10000 p (.push 28 (.stay 27)))
  rw [oldBefore29, at29, literal, oldAfter20, gammaAfter20]
  exact numeric
theorem numeric21 (p : Pattern) (guard : d56764 p = 1) (decreasing : d2671 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 29 p
  rw [at29] at beforeRange
  have afterRange := bonus_range 52 (HazardPattern.afterPattern 10000 p (.walk 52))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) ∧ bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) ≤ 2 at afterRange
  rw [gammaAfter21] at afterRange
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
theorem local21 (p : Pattern) (guard : d56764 p = 1)
    (decreasing : bonus 52 (HazardPattern.afterPattern 10000 p (.walk 52)) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 52) + NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 52))) + bonus 52 (HazardPattern.afterPattern 10000 p (.walk 52)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 52) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) < bonus 29 p at decreasing
  rw [gammaAfter21, at29] at decreasing
  have numeric := numeric21 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52))
  rw [oldBefore29, at29, literal, oldAfter21, gammaAfter21]
  exact numeric
theorem numeric22 (p : Pattern) (guard : d56770 p = 1) (decreasing : d3015 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d3015 p := by
  have beforeRange := bonus_range 29 p
  rw [at29] at beforeRange
  have afterRange := bonus_range 50 (HazardPattern.afterPattern 10000 p (.walk 50))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ∧ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ≤ 2 at afterRange
  rw [gammaAfter22] at afterRange
  have possibilities : (d2671 p = 1 ∧ d3015 p = 0) ∨ (d2671 p = 2 ∧ d3015 p = 0) ∨ (d2671 p = 2 ∧ d3015 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro1080 p beforeEq guard
    have complete := andIntro812 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro1081 p beforeEq guard
    have complete := andIntro834 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1406 p pair.2
    have combined := andIntro1081 p beforeEq guard
    have complete := andIntro835 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local22 (p : Pattern) (guard : d56770 p = 1)
    (decreasing : bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 50) + NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 50))) + bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 50) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 29 p at decreasing
  rw [gammaAfter22, at29] at decreasing
  have numeric := numeric22 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50))
  rw [oldBefore29, at29, literal, oldAfter22, gammaAfter22]
  exact numeric
theorem numeric23 (p : Pattern) (guard : d56771 p = 1) (decreasing : d2671 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 30 p
  rw [at30] at beforeRange
  have afterRange := bonus_range 52 (HazardPattern.afterPattern 10000 p (.walk 52))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) ∧ bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) ≤ 2 at afterRange
  rw [gammaAfter23] at afterRange
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
theorem local23 (p : Pattern) (guard : d56771 p = 1)
    (decreasing : bonus 52 (HazardPattern.afterPattern 10000 p (.walk 52)) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 52) + NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 52))) + bonus 52 (HazardPattern.afterPattern 10000 p (.walk 52)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 52) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52)) < bonus 30 p at decreasing
  rw [gammaAfter23, at30] at decreasing
  have numeric := numeric23 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 52)) (HazardPattern.afterPattern 10000 p (.walk 52))
  rw [oldBefore30, at30, literal, oldAfter23, gammaAfter23]
  exact numeric
theorem numeric24 (p : Pattern) (guard : d56776 p = 1) (decreasing : d57084 p < d2671 p) :
    d47911 p + d2671 p ≤ (1 : Int) + d47911 p + d57084 p := by
  have beforeRange := bonus_range 30 p
  rw [at30] at beforeRange
  have afterRange := bonus_range 52 (HazardPattern.afterPattern 10000 p (.push 52 (.stay 74)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 52 (.stay 74))) (HazardPattern.afterPattern 10000 p (.push 52 (.stay 74))) ∧ bonus (HazardPattern.nextHero (.push 52 (.stay 74))) (HazardPattern.afterPattern 10000 p (.push 52 (.stay 74))) ≤ 2 at afterRange
  rw [gammaAfter24] at afterRange
  have possibilities : (d2671 p = 1 ∧ d57084 p = 0) ∨ (d2671 p = 2 ∧ d57084 p = 0) ∨ (d2671 p = 2 ∧ d57084 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1617 p pair.2
    have combined := andIntro1085 p beforeEq guard
    have complete := andIntro1086 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1617 p pair.2
    have combined := andIntro1088 p beforeEq guard
    have complete := andIntro1086 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1652 p pair.2
    have combined := andIntro1088 p beforeEq guard
    have complete := andIntro1089 p combined afterEq
    have bound := compare11 p complete
    omega
theorem local24 (p : Pattern) (guard : d56776 p = 1)
    (decreasing : bonus 52 (HazardPattern.afterPattern 10000 p (.push 52 (.stay 74))) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 52 (.stay 74)) + NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 52 (.stay 74)))) + bonus 52 (HazardPattern.afterPattern 10000 p (.push 52 (.stay 74))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 52 (.stay 74)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 52 (.stay 74))) (HazardPattern.afterPattern 10000 p (.push 52 (.stay 74))) < bonus 30 p at decreasing
  rw [gammaAfter24, at30] at decreasing
  have numeric := numeric24 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 52 (.stay 74))) (HazardPattern.afterPattern 10000 p (.push 52 (.stay 74)))
  rw [oldBefore30, at30, literal, oldAfter24, gammaAfter24]
  exact numeric
theorem numeric25 (p : Pattern) (guard : d56756 p = 1) (decreasing : d2671 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 30 p
  rw [at30] at beforeRange
  have afterRange := bonus_range 29 (HazardPattern.afterPattern 10000 p (.walk 29))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) ∧ bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) ≤ 2 at afterRange
  rw [gammaAfter25] at afterRange
  have possibilities : (d2671 p = 1 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 0) ∨ (d2671 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1076 p beforeEq guard
    have complete := andIntro722 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1077 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro1077 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare9 p complete
    omega
theorem local25 (p : Pattern) (guard : d56756 p = 1)
    (decreasing : bonus 29 (HazardPattern.afterPattern 10000 p (.walk 29)) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 29) + NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 29))) + bonus 29 (HazardPattern.afterPattern 10000 p (.walk 29)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 29) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) < bonus 30 p at decreasing
  rw [gammaAfter25, at30] at decreasing
  have numeric := numeric25 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29))
  rw [oldBefore30, at30, literal, oldAfter25, gammaAfter25]
  exact numeric
theorem numeric26 (p : Pattern) (guard : d55886 p = 1) (decreasing : d0 p < d2671 p) :
    d47911 p + d2671 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 30 p
  rw [at30] at beforeRange
  have afterRange := bonus_range 29 (HazardPattern.afterPattern 10000 p (.push 29 (.stay 28)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 29 (.stay 28))) (HazardPattern.afterPattern 10000 p (.push 29 (.stay 28))) ∧ bonus (HazardPattern.nextHero (.push 29 (.stay 28))) (HazardPattern.afterPattern 10000 p (.push 29 (.stay 28))) ≤ 2 at afterRange
  rw [gammaAfter26] at afterRange
  have possibilities : (d2671 p = 1 ∧ d0 p = 0) ∨ (d2671 p = 2 ∧ d0 p = 0) ∨ (d2671 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro926 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare11 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro927 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro927 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local26 (p : Pattern) (guard : d55886 p = 1)
    (decreasing : bonus 29 (HazardPattern.afterPattern 10000 p (.push 29 (.stay 28))) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 29 (.stay 28)) + NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 29 (.stay 28)))) + bonus 29 (HazardPattern.afterPattern 10000 p (.push 29 (.stay 28))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 29 (.stay 28)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 29 (.stay 28))) (HazardPattern.afterPattern 10000 p (.push 29 (.stay 28))) < bonus 30 p at decreasing
  rw [gammaAfter26, at30] at decreasing
  have numeric := numeric26 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 29 (.stay 28))) (HazardPattern.afterPattern 10000 p (.push 29 (.stay 28)))
  rw [oldBefore30, at30, literal, oldAfter26, gammaAfter26]
  exact numeric
theorem numeric27 (p : Pattern) (guard : d57566 p = 1) (decreasing : d3142 p < d2671 p) :
    d47911 p + d2671 p ≤ (0 : Int) + d47911 p + d3142 p := by
  have beforeRange := bonus_range 30 p
  rw [at30] at beforeRange
  have afterRange := bonus_range 51 (HazardPattern.afterPattern 10000 p (.walk 51))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ∧ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ≤ 2 at afterRange
  rw [gammaAfter27] at afterRange
  have possibilities : (d2671 p = 1 ∧ d3142 p = 0) ∨ (d2671 p = 2 ∧ d3142 p = 0) ∨ (d2671 p = 2 ∧ d3142 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1187 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro1090 p beforeEq guard
    have complete := andIntro969 p afterEq combined
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro1091 p beforeEq guard
    have complete := andIntro991 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro1237 p pair.1
    have afterEq := eqIntro1448 p pair.2
    have combined := andIntro1091 p beforeEq guard
    have complete := andIntro1012 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local27 (p : Pattern) (guard : d57566 p = 1)
    (decreasing : bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 51) + NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 51))) + bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 51) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 30 p at decreasing
  rw [gammaAfter27, at30] at decreasing
  have numeric := numeric27 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51))
  rw [oldBefore30, at30, literal, oldAfter27, gammaAfter27]
  exact numeric
theorem numeric28 (p : Pattern) (guard : d57571 p = 1) (decreasing : d2518 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 45 p
  rw [at45] at beforeRange
  have afterRange := bonus_range 67 (HazardPattern.afterPattern 10000 p (.walk 67))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67)) ∧ bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67)) ≤ 2 at afterRange
  rw [gammaAfter28] at afterRange
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
theorem local28 (p : Pattern) (guard : d57571 p = 1)
    (decreasing : bonus 67 (HazardPattern.afterPattern 10000 p (.walk 67)) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 67) + NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 67))) + bonus 67 (HazardPattern.afterPattern 10000 p (.walk 67)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 67) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67)) < bonus 45 p at decreasing
  rw [gammaAfter28, at45] at decreasing
  have numeric := numeric28 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67))
  rw [oldBefore45, at45, literal, oldAfter28, gammaAfter28]
  exact numeric
theorem numeric29 (p : Pattern) (guard : d57576 p = 1) (decreasing : d57849 p < d2518 p) :
    d47866 p + d2518 p ≤ (1 : Int) + d47866 p + d57849 p := by
  have beforeRange := bonus_range 45 p
  rw [at45] at beforeRange
  have afterRange := bonus_range 67 (HazardPattern.afterPattern 10000 p (.push 67 (.stay 89)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 67 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 67 (.stay 89))) ∧ bonus (HazardPattern.nextHero (.push 67 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 67 (.stay 89))) ≤ 2 at afterRange
  rw [gammaAfter29] at afterRange
  have possibilities : (d2518 p = 1 ∧ d57849 p = 0) ∨ (d2518 p = 2 ∧ d57849 p = 0) ∨ (d2518 p = 2 ∧ d57849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1701 p pair.2
    have combined := andIntro1095 p beforeEq guard
    have complete := andIntro1096 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1701 p pair.2
    have combined := andIntro1098 p beforeEq guard
    have complete := andIntro1096 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1702 p pair.2
    have combined := andIntro1098 p beforeEq guard
    have complete := andIntro1099 p combined afterEq
    have bound := compare2 p complete
    omega
theorem local29 (p : Pattern) (guard : d57576 p = 1)
    (decreasing : bonus 67 (HazardPattern.afterPattern 10000 p (.push 67 (.stay 89))) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 67 (.stay 89)) + NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 67 (.stay 89)))) + bonus 67 (HazardPattern.afterPattern 10000 p (.push 67 (.stay 89))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 67 (.stay 89)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 67 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 67 (.stay 89))) < bonus 45 p at decreasing
  rw [gammaAfter29, at45] at decreasing
  have numeric := numeric29 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 67 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 67 (.stay 89)))
  rw [oldBefore45, at45, literal, oldAfter29, gammaAfter29]
  exact numeric
theorem numeric30 (p : Pattern) (guard : d58123 p = 1) (decreasing : d2518 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 45 p
  rw [at45] at beforeRange
  have afterRange := bonus_range 46 (HazardPattern.afterPattern 10000 p (.walk 46))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) ∧ bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) ≤ 2 at afterRange
  rw [gammaAfter30] at afterRange
  have possibilities : (d2518 p = 1 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1100 p beforeEq guard
    have complete := andIntro321 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1101 p beforeEq guard
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro1101 p beforeEq guard
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local30 (p : Pattern) (guard : d58123 p = 1)
    (decreasing : bonus 46 (HazardPattern.afterPattern 10000 p (.walk 46)) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 46) + NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 46))) + bonus 46 (HazardPattern.afterPattern 10000 p (.walk 46)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 46) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) < bonus 45 p at decreasing
  rw [gammaAfter30, at45] at decreasing
  have numeric := numeric30 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46))
  rw [oldBefore45, at45, literal, oldAfter30, gammaAfter30]
  exact numeric
theorem numeric31 (p : Pattern) (guard : d58126 p = 1) (decreasing : d0 p < d2518 p) :
    d47866 p + d2518 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 45 p
  rw [at45] at beforeRange
  have afterRange := bonus_range 46 (HazardPattern.afterPattern 10000 p (.push 46 (.stay 47)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 46 (.stay 47))) (HazardPattern.afterPattern 10000 p (.push 46 (.stay 47))) ∧ bonus (HazardPattern.nextHero (.push 46 (.stay 47))) (HazardPattern.afterPattern 10000 p (.push 46 (.stay 47))) ≤ 2 at afterRange
  rw [gammaAfter31] at afterRange
  have possibilities : (d2518 p = 1 ∧ d0 p = 0) ∨ (d2518 p = 2 ∧ d0 p = 0) ∨ (d2518 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro1103 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro1105 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro1105 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2 p complete
    omega
theorem local31 (p : Pattern) (guard : d58126 p = 1)
    (decreasing : bonus 46 (HazardPattern.afterPattern 10000 p (.push 46 (.stay 47))) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 46 (.stay 47)) + NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 46 (.stay 47)))) + bonus 46 (HazardPattern.afterPattern 10000 p (.push 46 (.stay 47))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 46 (.stay 47)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 46 (.stay 47))) (HazardPattern.afterPattern 10000 p (.push 46 (.stay 47))) < bonus 45 p at decreasing
  rw [gammaAfter31, at45] at decreasing
  have numeric := numeric31 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 46 (.stay 47))) (HazardPattern.afterPattern 10000 p (.push 46 (.stay 47)))
  rw [oldBefore45, at45, literal, oldAfter31, gammaAfter31]
  exact numeric
theorem numeric32 (p : Pattern) (guard : d54512 p = 1) (decreasing : d2518 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 46 p
  rw [at46] at beforeRange
  have afterRange := bonus_range 47 (HazardPattern.afterPattern 10000 p (.walk 47))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) ∧ bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) ≤ 2 at afterRange
  rw [gammaAfter32] at afterRange
  have possibilities : (d2518 p = 1 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1106 p beforeEq guard
    have complete := andIntro321 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1107 p beforeEq guard
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro1107 p beforeEq guard
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local32 (p : Pattern) (guard : d54512 p = 1)
    (decreasing : bonus 47 (HazardPattern.afterPattern 10000 p (.walk 47)) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 47) + NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 47))) + bonus 47 (HazardPattern.afterPattern 10000 p (.walk 47)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 47) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) < bonus 46 p at decreasing
  rw [gammaAfter32, at46] at decreasing
  have numeric := numeric32 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47))
  rw [oldBefore46, at46, literal, oldAfter32, gammaAfter32]
  exact numeric
theorem numeric33 (p : Pattern) (guard : d58129 p = 1) (decreasing : d58231 p < d2518 p) :
    d47866 p + d2518 p ≤ (1 : Int) + d47865 p + d58231 p := by
  have beforeRange := bonus_range 46 p
  rw [at46] at beforeRange
  have afterRange := bonus_range 47 (HazardPattern.afterPattern 10000 p (.push 47 (.stay 48)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 47 (.stay 48))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 48))) ∧ bonus (HazardPattern.nextHero (.push 47 (.stay 48))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 48))) ≤ 2 at afterRange
  rw [gammaAfter33] at afterRange
  have possibilities : (d2518 p = 1 ∧ d58231 p = 0) ∨ (d2518 p = 2 ∧ d58231 p = 0) ∨ (d2518 p = 2 ∧ d58231 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1724 p pair.2
    have combined := andIntro1109 p beforeEq guard
    have complete := andIntro1110 p combined afterEq
    have bound := compare14 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1724 p pair.2
    have combined := andIntro1112 p beforeEq guard
    have complete := andIntro1110 p combined afterEq
    have bound := compare15 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1745 p pair.2
    have combined := andIntro1112 p beforeEq guard
    have complete := andIntro1113 p combined afterEq
    have bound := compare14 p complete
    omega
theorem local33 (p : Pattern) (guard : d58129 p = 1)
    (decreasing : bonus 47 (HazardPattern.afterPattern 10000 p (.push 47 (.stay 48))) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 47 (.stay 48)) + NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 47 (.stay 48)))) + bonus 47 (HazardPattern.afterPattern 10000 p (.push 47 (.stay 48))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 47 (.stay 48)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 47 (.stay 48))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 48))) < bonus 46 p at decreasing
  rw [gammaAfter33, at46] at decreasing
  have numeric := numeric33 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 47 (.stay 48))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 48)))
  rw [oldBefore46, at46, literal, oldAfter33, gammaAfter33]
  exact numeric
theorem numeric34 (p : Pattern) (guard : d58123 p = 1) (decreasing : d2518 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 46 p
  rw [at46] at beforeRange
  have afterRange := bonus_range 45 (HazardPattern.afterPattern 10000 p (.walk 45))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 45)) (HazardPattern.afterPattern 10000 p (.walk 45)) ∧ bonus (HazardPattern.nextHero (.walk 45)) (HazardPattern.afterPattern 10000 p (.walk 45)) ≤ 2 at afterRange
  rw [gammaAfter34] at afterRange
  have possibilities : (d2518 p = 1 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1100 p beforeEq guard
    have complete := andIntro321 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1101 p beforeEq guard
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro1101 p beforeEq guard
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local34 (p : Pattern) (guard : d58123 p = 1)
    (decreasing : bonus 45 (HazardPattern.afterPattern 10000 p (.walk 45)) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 45) + NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 45))) + bonus 45 (HazardPattern.afterPattern 10000 p (.walk 45)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 45) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 45)) (HazardPattern.afterPattern 10000 p (.walk 45)) < bonus 46 p at decreasing
  rw [gammaAfter34, at46] at decreasing
  have numeric := numeric34 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 45)) (HazardPattern.afterPattern 10000 p (.walk 45))
  rw [oldBefore46, at46, literal, oldAfter34, gammaAfter34]
  exact numeric
theorem numeric35 (p : Pattern) (guard : d54513 p = 1) (decreasing : d2518 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 46 p
  rw [at46] at beforeRange
  have afterRange := bonus_range 25 (HazardPattern.afterPattern 10000 p (.walk 25))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 25)) (HazardPattern.afterPattern 10000 p (.walk 25)) ∧ bonus (HazardPattern.nextHero (.walk 25)) (HazardPattern.afterPattern 10000 p (.walk 25)) ≤ 2 at afterRange
  rw [gammaAfter35] at afterRange
  have possibilities : (d2518 p = 1 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro534 p beforeEq guard
    have complete := andIntro321 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro535 p beforeEq guard
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro535 p beforeEq guard
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local35 (p : Pattern) (guard : d54513 p = 1)
    (decreasing : bonus 25 (HazardPattern.afterPattern 10000 p (.walk 25)) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 25) + NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 25))) + bonus 25 (HazardPattern.afterPattern 10000 p (.walk 25)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 25) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 25)) (HazardPattern.afterPattern 10000 p (.walk 25)) < bonus 46 p at decreasing
  rw [gammaAfter35, at46] at decreasing
  have numeric := numeric35 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 25)) (HazardPattern.afterPattern 10000 p (.walk 25))
  rw [oldBefore46, at46, literal, oldAfter35, gammaAfter35]
  exact numeric
theorem numeric36 (p : Pattern) (guard : d58433 p = 1) (decreasing : d3318 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d3318 p := by
  have beforeRange := bonus_range 46 p
  rw [at46] at beforeRange
  have afterRange := bonus_range 69 (HazardPattern.afterPattern 10000 p (.walk 69))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) ∧ bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) ≤ 2 at afterRange
  rw [gammaAfter36] at afterRange
  have possibilities : (d2518 p = 1 ∧ d3318 p = 0) ∨ (d2518 p = 2 ∧ d3318 p = 0) ∨ (d2518 p = 2 ∧ d3318 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1766 p pair.2
    have combined := andIntro1134 p beforeEq guard
    have complete := andIntro1155 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1766 p pair.2
    have combined := andIntro1156 p beforeEq guard
    have complete := andIntro1177 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1787 p pair.2
    have combined := andIntro1156 p beforeEq guard
    have complete := andIntro1198 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local36 (p : Pattern) (guard : d58433 p = 1)
    (decreasing : bonus 69 (HazardPattern.afterPattern 10000 p (.walk 69)) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 69) + NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 69))) + bonus 69 (HazardPattern.afterPattern 10000 p (.walk 69)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 69) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) < bonus 46 p at decreasing
  rw [gammaAfter36, at46] at decreasing
  have numeric := numeric36 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69))
  rw [oldBefore46, at46, literal, oldAfter36, gammaAfter36]
  exact numeric
theorem numeric37 (p : Pattern) (guard : d58745 p = 1) (decreasing : d2518 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 46 p
  rw [at46] at beforeRange
  have afterRange := bonus_range 67 (HazardPattern.afterPattern 10000 p (.walk 67))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67)) ∧ bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67)) ≤ 2 at afterRange
  rw [gammaAfter37] at afterRange
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
theorem local37 (p : Pattern) (guard : d58745 p = 1)
    (decreasing : bonus 67 (HazardPattern.afterPattern 10000 p (.walk 67)) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 67) + NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 67))) + bonus 67 (HazardPattern.afterPattern 10000 p (.walk 67)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 67) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67)) < bonus 46 p at decreasing
  rw [gammaAfter37, at46] at decreasing
  have numeric := numeric37 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 67)) (HazardPattern.afterPattern 10000 p (.walk 67))
  rw [oldBefore46, at46, literal, oldAfter37, gammaAfter37]
  exact numeric
theorem numeric38 (p : Pattern) (guard : d51640 p = 1) (decreasing : d2518 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 47 p
  rw [at47] at beforeRange
  have afterRange := bonus_range 25 (HazardPattern.afterPattern 10000 p (.walk 25))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 25)) (HazardPattern.afterPattern 10000 p (.walk 25)) ∧ bonus (HazardPattern.nextHero (.walk 25)) (HazardPattern.afterPattern 10000 p (.walk 25)) ≤ 2 at afterRange
  rw [gammaAfter38] at afterRange
  have possibilities : (d2518 p = 1 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro0 p guard beforeEq
    have complete := andIntro321 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro322 p guard beforeEq
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro322 p guard beforeEq
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local38 (p : Pattern) (guard : d51640 p = 1)
    (decreasing : bonus 25 (HazardPattern.afterPattern 10000 p (.walk 25)) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 25) + NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 25))) + bonus 25 (HazardPattern.afterPattern 10000 p (.walk 25)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 25) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 25)) (HazardPattern.afterPattern 10000 p (.walk 25)) < bonus 47 p at decreasing
  rw [gammaAfter38, at47] at decreasing
  have numeric := numeric38 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 25)) (HazardPattern.afterPattern 10000 p (.walk 25))
  rw [oldBefore47, at47, literal, oldAfter38, gammaAfter38]
  exact numeric
theorem numeric39 (p : Pattern) (guard : d58432 p = 1) (decreasing : d3318 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d3318 p := by
  have beforeRange := bonus_range 47 p
  rw [at47] at beforeRange
  have afterRange := bonus_range 69 (HazardPattern.afterPattern 10000 p (.walk 69))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) ∧ bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) ≤ 2 at afterRange
  rw [gammaAfter39] at afterRange
  have possibilities : (d2518 p = 1 ∧ d3318 p = 0) ∨ (d2518 p = 2 ∧ d3318 p = 0) ∨ (d2518 p = 2 ∧ d3318 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1766 p pair.2
    have combined := andIntro1202 p beforeEq guard
    have complete := andIntro1155 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1766 p pair.2
    have combined := andIntro1203 p beforeEq guard
    have complete := andIntro1177 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1787 p pair.2
    have combined := andIntro1203 p beforeEq guard
    have complete := andIntro1198 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local39 (p : Pattern) (guard : d58432 p = 1)
    (decreasing : bonus 69 (HazardPattern.afterPattern 10000 p (.walk 69)) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 69) + NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 69))) + bonus 69 (HazardPattern.afterPattern 10000 p (.walk 69)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 69) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) < bonus 47 p at decreasing
  rw [gammaAfter39, at47] at decreasing
  have numeric := numeric39 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69))
  rw [oldBefore47, at47, literal, oldAfter39, gammaAfter39]
  exact numeric
theorem numeric40 (p : Pattern) (guard : d58750 p = 1) (decreasing : d59195 p < d2518 p) :
    d47866 p + d2518 p ≤ (1 : Int) + d47866 p + d59195 p := by
  have beforeRange := bonus_range 47 p
  rw [at47] at beforeRange
  have afterRange := bonus_range 69 (HazardPattern.afterPattern 10000 p (.push 69 (.stay 91)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 69 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 69 (.stay 91))) ∧ bonus (HazardPattern.nextHero (.push 69 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 69 (.stay 91))) ≤ 2 at afterRange
  rw [gammaAfter40] at afterRange
  have possibilities : (d2518 p = 1 ∧ d59195 p = 0) ∨ (d2518 p = 2 ∧ d59195 p = 0) ∨ (d2518 p = 2 ∧ d59195 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1848 p pair.2
    have combined := andIntro1231 p beforeEq guard
    have complete := andIntro1275 p afterEq combined
    have bound := compare16 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1848 p pair.2
    have combined := andIntro1296 p beforeEq guard
    have complete := andIntro1297 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1892 p pair.2
    have combined := andIntro1296 p beforeEq guard
    have complete := andIntro1298 p combined afterEq
    have bound := compare2 p complete
    omega
theorem local40 (p : Pattern) (guard : d58750 p = 1)
    (decreasing : bonus 69 (HazardPattern.afterPattern 10000 p (.push 69 (.stay 91))) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 69 (.stay 91)) + NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 69 (.stay 91)))) + bonus 69 (HazardPattern.afterPattern 10000 p (.push 69 (.stay 91))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 69 (.stay 91)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 69 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 69 (.stay 91))) < bonus 47 p at decreasing
  rw [gammaAfter40, at47] at decreasing
  have numeric := numeric40 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 69 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 69 (.stay 91)))
  rw [oldBefore47, at47, literal, oldAfter40, gammaAfter40]
  exact numeric
theorem numeric41 (p : Pattern) (guard : d54185 p = 1) (decreasing : d2782 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d48080 p + d2782 p := by
  have beforeRange := bonus_range 47 p
  rw [at47] at beforeRange
  have afterRange := bonus_range 48 (HazardPattern.afterPattern 10000 p (.walk 48))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ∧ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ≤ 2 at afterRange
  rw [gammaAfter41] at afterRange
  have possibilities : (d2518 p = 1 ∧ d2782 p = 0) ∨ (d2518 p = 2 ∧ d2782 p = 0) ∨ (d2518 p = 2 ∧ d2782 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro1299 p beforeEq guard
    have complete := andIntro470 p afterEq combined
    have bound := compare3 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro1300 p beforeEq guard
    have complete := andIntro512 p afterEq combined
    have bound := compare4 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1166 p pair.2
    have combined := andIntro1300 p beforeEq guard
    have complete := andIntro533 p afterEq combined
    have bound := compare3 p complete
    omega
theorem local41 (p : Pattern) (guard : d54185 p = 1)
    (decreasing : bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 48) + NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 48))) + bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 48) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 47 p at decreasing
  rw [gammaAfter41, at47] at decreasing
  have numeric := numeric41 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48))
  rw [oldBefore47, at47, literal, oldAfter41, gammaAfter41]
  exact numeric
theorem numeric42 (p : Pattern) (guard : d60241 p = 1) (decreasing : d60344 p < d2518 p) :
    d47866 p + d2518 p ≤ (1 : Int) + d47767 p + d60344 p := by
  have beforeRange := bonus_range 47 p
  rw [at47] at beforeRange
  have afterRange := bonus_range 48 (HazardPattern.afterPattern 10000 p (.push 48 (.stay 49)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 48 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 48 (.stay 49))) ∧ bonus (HazardPattern.nextHero (.push 48 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 48 (.stay 49))) ≤ 2 at afterRange
  rw [gammaAfter42] at afterRange
  have possibilities : (d2518 p = 1 ∧ d60344 p = 0) ∨ (d2518 p = 2 ∧ d60344 p = 0) ∨ (d2518 p = 2 ∧ d60344 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1914 p pair.2
    have combined := andIntro1322 p beforeEq guard
    have complete := andIntro1414 p afterEq combined
    have bound := compare1127 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1914 p pair.2
    have combined := andIntro1435 p beforeEq guard
    have complete := andIntro1463 p afterEq combined
    have bound := compare2042 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1935 p pair.2
    have combined := andIntro1435 p beforeEq guard
    have complete := andIntro1491 p combined afterEq
    have bound := compare17 p complete
    omega
theorem local42 (p : Pattern) (guard : d60241 p = 1)
    (decreasing : bonus 48 (HazardPattern.afterPattern 10000 p (.push 48 (.stay 49))) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 48 (.stay 49)) + NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 48 (.stay 49)))) + bonus 48 (HazardPattern.afterPattern 10000 p (.push 48 (.stay 49))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 48 (.stay 49)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 48 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 48 (.stay 49))) < bonus 47 p at decreasing
  rw [gammaAfter42, at47] at decreasing
  have numeric := numeric42 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 48 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 48 (.stay 49)))
  rw [oldBefore47, at47, literal, oldAfter42, gammaAfter42]
  exact numeric
theorem numeric43 (p : Pattern) (guard : d54512 p = 1) (decreasing : d2518 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 47 p
  rw [at47] at beforeRange
  have afterRange := bonus_range 46 (HazardPattern.afterPattern 10000 p (.walk 46))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) ∧ bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) ≤ 2 at afterRange
  rw [gammaAfter43] at afterRange
  have possibilities : (d2518 p = 1 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 0) ∨ (d2518 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1106 p beforeEq guard
    have complete := andIntro321 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1107 p beforeEq guard
    have complete := andIntro371 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro1107 p beforeEq guard
    have complete := andIntro420 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local43 (p : Pattern) (guard : d54512 p = 1)
    (decreasing : bonus 46 (HazardPattern.afterPattern 10000 p (.walk 46)) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 46) + NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 46))) + bonus 46 (HazardPattern.afterPattern 10000 p (.walk 46)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 46) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46)) < bonus 47 p at decreasing
  rw [gammaAfter43, at47] at decreasing
  have numeric := numeric43 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 46)) (HazardPattern.afterPattern 10000 p (.walk 46))
  rw [oldBefore47, at47, literal, oldAfter43, gammaAfter43]
  exact numeric
theorem numeric44 (p : Pattern) (guard : d58126 p = 1) (decreasing : d0 p < d2518 p) :
    d47866 p + d2518 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 47 p
  rw [at47] at beforeRange
  have afterRange := bonus_range 46 (HazardPattern.afterPattern 10000 p (.push 46 (.stay 45)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 46 (.stay 45))) (HazardPattern.afterPattern 10000 p (.push 46 (.stay 45))) ∧ bonus (HazardPattern.nextHero (.push 46 (.stay 45))) (HazardPattern.afterPattern 10000 p (.push 46 (.stay 45))) ≤ 2 at afterRange
  rw [gammaAfter44] at afterRange
  have possibilities : (d2518 p = 1 ∧ d0 p = 0) ∨ (d2518 p = 2 ∧ d0 p = 0) ∨ (d2518 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro1103 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare2 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro1105 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro1105 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2 p complete
    omega
theorem local44 (p : Pattern) (guard : d58126 p = 1)
    (decreasing : bonus 46 (HazardPattern.afterPattern 10000 p (.push 46 (.stay 45))) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 46 (.stay 45)) + NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 46 (.stay 45)))) + bonus 46 (HazardPattern.afterPattern 10000 p (.push 46 (.stay 45))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 46 (.stay 45)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 46 (.stay 45))) (HazardPattern.afterPattern 10000 p (.push 46 (.stay 45))) < bonus 47 p at decreasing
  rw [gammaAfter44, at47] at decreasing
  have numeric := numeric44 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 46 (.stay 45))) (HazardPattern.afterPattern 10000 p (.push 46 (.stay 45)))
  rw [oldBefore47, at47, literal, oldAfter44, gammaAfter44]
  exact numeric
theorem numeric45 (p : Pattern) (guard : d61360 p = 1) (decreasing : d3496 p < d2518 p) :
    d47866 p + d2518 p ≤ (0 : Int) + d47866 p + d3496 p := by
  have beforeRange := bonus_range 47 p
  rw [at47] at beforeRange
  have afterRange := bonus_range 70 (HazardPattern.afterPattern 10000 p (.walk 70))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ∧ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ≤ 2 at afterRange
  rw [gammaAfter45] at afterRange
  have possibilities : (d2518 p = 1 ∧ d3496 p = 0) ∨ (d2518 p = 2 ∧ d3496 p = 0) ∨ (d2518 p = 2 ∧ d3496 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro185 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro1513 p beforeEq guard
    have complete := andIntro1535 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro1556 p beforeEq guard
    have complete := andIntro1577 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro1101 p pair.1
    have afterEq := eqIntro1978 p pair.2
    have combined := andIntro1556 p beforeEq guard
    have complete := andIntro1598 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local45 (p : Pattern) (guard : d61360 p = 1)
    (decreasing : bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 70) + NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 70))) + bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 70) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 47 p at decreasing
  rw [gammaAfter45, at47] at decreasing
  have numeric := numeric45 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70))
  rw [oldBefore47, at47, literal, oldAfter45, gammaAfter45]
  exact numeric
theorem numeric46 (p : Pattern) (guard : d61807 p = 1) (decreasing : d3496 p < d2782 p) :
    d48080 p + d2782 p ≤ (0 : Int) + d47866 p + d3496 p := by
  have beforeRange := bonus_range 48 p
  rw [at48] at beforeRange
  have afterRange := bonus_range 70 (HazardPattern.afterPattern 10000 p (.walk 70))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ∧ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ≤ 2 at afterRange
  rw [gammaAfter46] at afterRange
  have possibilities : (d2782 p = 1 ∧ d3496 p = 0) ∨ (d2782 p = 2 ∧ d3496 p = 0) ∨ (d2782 p = 2 ∧ d3496 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1166 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro1620 p beforeEq guard
    have complete := andIntro1535 p afterEq combined
    have bound := compare2043 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro1641 p beforeEq guard
    have complete := andIntro1577 p afterEq combined
    have bound := compare2044 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro1978 p pair.2
    have combined := andIntro1641 p beforeEq guard
    have complete := andIntro1598 p afterEq combined
    have bound := compare2043 p complete
    omega
theorem local46 (p : Pattern) (guard : d61807 p = 1)
    (decreasing : bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 70) + NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 70))) + bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 70) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 48 p at decreasing
  rw [gammaAfter46, at48] at decreasing
  have numeric := numeric46 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70))
  rw [oldBefore48, at48, literal, oldAfter46, gammaAfter46]
  exact numeric
theorem numeric47 (p : Pattern) (guard : d55878 p = 1) (decreasing : d2895 p < d2782 p) :
    d48080 p + d2782 p ≤ (0 : Int) + d48083 p + d2895 p := by
  have beforeRange := bonus_range 48 p
  rw [at48] at beforeRange
  have afterRange := bonus_range 49 (HazardPattern.afterPattern 10000 p (.walk 49))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) ∧ bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) ≤ 2 at afterRange
  rw [gammaAfter47] at afterRange
  have possibilities : (d2782 p = 1 ∧ d2895 p = 0) ∨ (d2782 p = 2 ∧ d2895 p = 0) ∨ (d2782 p = 2 ∧ d2895 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1166 p pair.1
    have afterEq := eqIntro1209 p pair.2
    have combined := andIntro1663 p beforeEq guard
    have complete := andIntro578 p afterEq combined
    have bound := compare2045 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro1209 p pair.2
    have combined := andIntro1684 p beforeEq guard
    have complete := andIntro600 p afterEq combined
    have bound := compare2046 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro1258 p pair.2
    have combined := andIntro1684 p beforeEq guard
    have complete := andIntro621 p afterEq combined
    have bound := compare2045 p complete
    omega
theorem local47 (p : Pattern) (guard : d55878 p = 1)
    (decreasing : bonus 49 (HazardPattern.afterPattern 10000 p (.walk 49)) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 49) + NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 49))) + bonus 49 (HazardPattern.afterPattern 10000 p (.walk 49)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 49) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) < bonus 48 p at decreasing
  rw [gammaAfter47, at48] at decreasing
  have numeric := numeric47 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49))
  rw [oldBefore48, at48, literal, oldAfter47, gammaAfter47]
  exact numeric
theorem numeric48 (p : Pattern) (guard : d61810 p = 1) (decreasing : d61921 p < d2782 p) :
    d48080 p + d2782 p ≤ (1 : Int) + d47700 p + d61921 p := by
  have beforeRange := bonus_range 48 p
  rw [at48] at beforeRange
  have afterRange := bonus_range 49 (HazardPattern.afterPattern 10000 p (.push 49 (.stay 50)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 49 (.stay 50))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 50))) ∧ bonus (HazardPattern.nextHero (.push 49 (.stay 50))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 50))) ≤ 2 at afterRange
  rw [gammaAfter48] at afterRange
  have possibilities : (d2782 p = 1 ∧ d61921 p = 0) ∨ (d2782 p = 2 ∧ d61921 p = 0) ∨ (d2782 p = 2 ∧ d61921 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1166 p pair.1
    have afterEq := eqIntro2022 p pair.2
    have combined := andIntro1706 p beforeEq guard
    have complete := andIntro1742 p afterEq combined
    have bound := compare2047 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro2022 p pair.2
    have combined := andIntro1763 p beforeEq guard
    have complete := andIntro1791 p afterEq combined
    have bound := compare2048 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro2043 p pair.2
    have combined := andIntro1763 p beforeEq guard
    have complete := andIntro1819 p combined afterEq
    have bound := compare2047 p complete
    omega
theorem local48 (p : Pattern) (guard : d61810 p = 1)
    (decreasing : bonus 49 (HazardPattern.afterPattern 10000 p (.push 49 (.stay 50))) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 49 (.stay 50)) + NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 49 (.stay 50)))) + bonus 49 (HazardPattern.afterPattern 10000 p (.push 49 (.stay 50))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 49 (.stay 50)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 49 (.stay 50))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 50))) < bonus 48 p at decreasing
  rw [gammaAfter48, at48] at decreasing
  have numeric := numeric48 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 49 (.stay 50))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 50)))
  rw [oldBefore48, at48, literal, oldAfter48, gammaAfter48]
  exact numeric
theorem numeric49 (p : Pattern) (guard : d54185 p = 1) (decreasing : d2518 p < d2782 p) :
    d48080 p + d2782 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 48 p
  rw [at48] at beforeRange
  have afterRange := bonus_range 47 (HazardPattern.afterPattern 10000 p (.walk 47))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) ∧ bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) ≤ 2 at afterRange
  rw [gammaAfter49] at afterRange
  have possibilities : (d2782 p = 1 ∧ d2518 p = 0) ∨ (d2782 p = 2 ∧ d2518 p = 0) ∨ (d2782 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1166 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1820 p guard beforeEq
    have complete := andIntro1842 p afterEq combined
    have bound := compare2043 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1843 p guard beforeEq
    have complete := andIntro1864 p afterEq combined
    have bound := compare2044 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro1843 p guard beforeEq
    have complete := andIntro1885 p afterEq combined
    have bound := compare2043 p complete
    omega
theorem local49 (p : Pattern) (guard : d54185 p = 1)
    (decreasing : bonus 47 (HazardPattern.afterPattern 10000 p (.walk 47)) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 47) + NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 47))) + bonus 47 (HazardPattern.afterPattern 10000 p (.walk 47)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 47) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47)) < bonus 48 p at decreasing
  rw [gammaAfter49, at48] at decreasing
  have numeric := numeric49 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 47)) (HazardPattern.afterPattern 10000 p (.walk 47))
  rw [oldBefore48, at48, literal, oldAfter49, gammaAfter49]
  exact numeric
theorem numeric50 (p : Pattern) (guard : d58129 p = 1) (decreasing : d0 p < d2782 p) :
    d48080 p + d2782 p ≤ (1 : Int) + d47866 p + d0 p := by
  have beforeRange := bonus_range 48 p
  rw [at48] at beforeRange
  have afterRange := bonus_range 47 (HazardPattern.afterPattern 10000 p (.push 47 (.stay 46)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 47 (.stay 46))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 46))) ∧ bonus (HazardPattern.nextHero (.push 47 (.stay 46))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 46))) ≤ 2 at afterRange
  rw [gammaAfter50] at afterRange
  have possibilities : (d2782 p = 1 ∧ d0 p = 0) ∨ (d2782 p = 2 ∧ d0 p = 0) ∨ (d2782 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1166 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro1887 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare2049 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro1889 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare2043 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro1889 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2049 p complete
    omega
theorem local50 (p : Pattern) (guard : d58129 p = 1)
    (decreasing : bonus 47 (HazardPattern.afterPattern 10000 p (.push 47 (.stay 46))) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 47 (.stay 46)) + NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 47 (.stay 46)))) + bonus 47 (HazardPattern.afterPattern 10000 p (.push 47 (.stay 46))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 47 (.stay 46)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 47 (.stay 46))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 46))) < bonus 48 p at decreasing
  rw [gammaAfter50, at48] at decreasing
  have numeric := numeric50 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 47 (.stay 46))) (HazardPattern.afterPattern 10000 p (.push 47 (.stay 46)))
  rw [oldBefore48, at48, literal, oldAfter50, gammaAfter50]
  exact numeric
theorem numeric51 (p : Pattern) (guard : d55879 p = 1) (decreasing : d2671 p < d2782 p) :
    d48080 p + d2782 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 48 p
  rw [at48] at beforeRange
  have afterRange := bonus_range 27 (HazardPattern.afterPattern 10000 p (.walk 27))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27)) ∧ bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27)) ≤ 2 at afterRange
  rw [gammaAfter51] at afterRange
  have possibilities : (d2782 p = 1 ∧ d2671 p = 0) ∨ (d2782 p = 2 ∧ d2671 p = 0) ∨ (d2782 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1166 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1890 p beforeEq guard
    have complete := andIntro1911 p combined afterEq
    have bound := compare2050 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1912 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare2051 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro1912 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare2050 p complete
    omega
theorem local51 (p : Pattern) (guard : d55879 p = 1)
    (decreasing : bonus 27 (HazardPattern.afterPattern 10000 p (.walk 27)) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 27) + NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 27))) + bonus 27 (HazardPattern.afterPattern 10000 p (.walk 27)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 27) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27)) < bonus 48 p at decreasing
  rw [gammaAfter51, at48] at decreasing
  have numeric := numeric51 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27))
  rw [oldBefore48, at48, literal, oldAfter51, gammaAfter51]
  exact numeric
theorem numeric52 (p : Pattern) (guard : d54186 p = 1) (decreasing : d2518 p < d2782 p) :
    d48080 p + d2782 p ≤ (0 : Int) + d47866 p + d2518 p := by
  have beforeRange := bonus_range 48 p
  rw [at48] at beforeRange
  have afterRange := bonus_range 25 (HazardPattern.afterPattern 10000 p (.walk 25))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 25)) (HazardPattern.afterPattern 10000 p (.walk 25)) ∧ bonus (HazardPattern.nextHero (.walk 25)) (HazardPattern.afterPattern 10000 p (.walk 25)) ≤ 2 at afterRange
  rw [gammaAfter52] at afterRange
  have possibilities : (d2782 p = 1 ∧ d2518 p = 0) ∨ (d2782 p = 2 ∧ d2518 p = 0) ∨ (d2782 p = 2 ∧ d2518 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1166 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1913 p guard beforeEq
    have complete := andIntro1842 p afterEq combined
    have bound := compare2043 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro643 p pair.2
    have combined := andIntro1914 p guard beforeEq
    have complete := andIntro1864 p afterEq combined
    have bound := compare2044 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro185 p pair.2
    have combined := andIntro1914 p guard beforeEq
    have complete := andIntro1885 p afterEq combined
    have bound := compare2043 p complete
    omega
theorem local52 (p : Pattern) (guard : d54186 p = 1)
    (decreasing : bonus 25 (HazardPattern.afterPattern 10000 p (.walk 25)) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 25) + NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 25))) + bonus 25 (HazardPattern.afterPattern 10000 p (.walk 25)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 25) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 25)) (HazardPattern.afterPattern 10000 p (.walk 25)) < bonus 48 p at decreasing
  rw [gammaAfter52, at48] at decreasing
  have numeric := numeric52 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 25)) (HazardPattern.afterPattern 10000 p (.walk 25))
  rw [oldBefore48, at48, literal, oldAfter52, gammaAfter52]
  exact numeric
theorem numeric53 (p : Pattern) (guard : d62376 p = 1) (decreasing : d3673 p < d2782 p) :
    d48080 p + d2782 p ≤ (0 : Int) + d48087 p + d3673 p := by
  have beforeRange := bonus_range 48 p
  rw [at48] at beforeRange
  have afterRange := bonus_range 71 (HazardPattern.afterPattern 10000 p (.walk 71))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) ∧ bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) ≤ 2 at afterRange
  rw [gammaAfter53] at afterRange
  have possibilities : (d2782 p = 1 ∧ d3673 p = 0) ∨ (d2782 p = 2 ∧ d3673 p = 0) ∨ (d2782 p = 2 ∧ d3673 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1166 p pair.1
    have afterEq := eqIntro2078 p pair.2
    have combined := andIntro1977 p beforeEq guard
    have complete := andIntro2012 p afterEq combined
    have bound := compare2052 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro2078 p pair.2
    have combined := andIntro2033 p beforeEq guard
    have complete := andIntro2061 p afterEq combined
    have bound := compare2053 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro2106 p pair.2
    have combined := andIntro2033 p beforeEq guard
    have complete := andIntro2089 p afterEq combined
    have bound := compare2052 p complete
    omega
theorem local53 (p : Pattern) (guard : d62376 p = 1)
    (decreasing : bonus 71 (HazardPattern.afterPattern 10000 p (.walk 71)) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 71) + NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 71))) + bonus 71 (HazardPattern.afterPattern 10000 p (.walk 71)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 71) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) < bonus 48 p at decreasing
  rw [gammaAfter53, at48] at decreasing
  have numeric := numeric53 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71))
  rw [oldBefore48, at48, literal, oldAfter53, gammaAfter53]
  exact numeric
theorem numeric54 (p : Pattern) (guard : d62827 p = 1) (decreasing : d3318 p < d2782 p) :
    d48080 p + d2782 p ≤ (0 : Int) + d47866 p + d3318 p := by
  have beforeRange := bonus_range 48 p
  rw [at48] at beforeRange
  have afterRange := bonus_range 69 (HazardPattern.afterPattern 10000 p (.walk 69))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) ∧ bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) ≤ 2 at afterRange
  rw [gammaAfter54] at afterRange
  have possibilities : (d2782 p = 1 ∧ d3318 p = 0) ∨ (d2782 p = 2 ∧ d3318 p = 0) ∨ (d2782 p = 2 ∧ d3318 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1166 p pair.1
    have afterEq := eqIntro1766 p pair.2
    have combined := andIntro2110 p beforeEq guard
    have complete := andIntro2131 p afterEq combined
    have bound := compare2043 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro1766 p pair.2
    have combined := andIntro2132 p beforeEq guard
    have complete := andIntro2153 p combined afterEq
    have bound := compare2044 p complete
    omega
  · have beforeEq := eqIntro2000 p pair.1
    have afterEq := eqIntro1787 p pair.2
    have combined := andIntro2132 p beforeEq guard
    have complete := andIntro2174 p combined afterEq
    have bound := compare2043 p complete
    omega
theorem local54 (p : Pattern) (guard : d62827 p = 1)
    (decreasing : bonus 69 (HazardPattern.afterPattern 10000 p (.walk 69)) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 69) + NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 69))) + bonus 69 (HazardPattern.afterPattern 10000 p (.walk 69)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 69) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69)) < bonus 48 p at decreasing
  rw [gammaAfter54, at48] at decreasing
  have numeric := numeric54 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 69)) (HazardPattern.afterPattern 10000 p (.walk 69))
  rw [oldBefore48, at48, literal, oldAfter54, gammaAfter54]
  exact numeric
theorem numeric55 (p : Pattern) (guard : d54518 p = 1) (decreasing : d2671 p < d2895 p) :
    d48083 p + d2895 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 49 p
  rw [at49] at beforeRange
  have afterRange := bonus_range 27 (HazardPattern.afterPattern 10000 p (.walk 27))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27)) ∧ bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27)) ≤ 2 at afterRange
  rw [gammaAfter55] at afterRange
  have possibilities : (d2895 p = 1 ∧ d2671 p = 0) ∨ (d2895 p = 2 ∧ d2671 p = 0) ∨ (d2895 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1258 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro2175 p guard beforeEq
    have complete := andIntro1911 p combined afterEq
    have bound := compare2054 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro579 p guard beforeEq
    have complete := andIntro744 p combined afterEq
    have bound := compare2055 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro579 p guard beforeEq
    have complete := andIntro765 p afterEq combined
    have bound := compare2054 p complete
    omega
theorem local55 (p : Pattern) (guard : d54518 p = 1)
    (decreasing : bonus 27 (HazardPattern.afterPattern 10000 p (.walk 27)) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 27) + NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 27))) + bonus 27 (HazardPattern.afterPattern 10000 p (.walk 27)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 27) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27)) < bonus 49 p at decreasing
  rw [gammaAfter55, at49] at decreasing
  have numeric := numeric55 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 27)) (HazardPattern.afterPattern 10000 p (.walk 27))
  rw [oldBefore49, at49, literal, oldAfter55, gammaAfter55]
  exact numeric
theorem numeric56 (p : Pattern) (guard : d62934 p = 1) (decreasing : d3673 p < d2895 p) :
    d48083 p + d2895 p ≤ (0 : Int) + d48087 p + d3673 p := by
  have beforeRange := bonus_range 49 p
  rw [at49] at beforeRange
  have afterRange := bonus_range 71 (HazardPattern.afterPattern 10000 p (.walk 71))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) ∧ bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) ≤ 2 at afterRange
  rw [gammaAfter56] at afterRange
  have possibilities : (d2895 p = 1 ∧ d3673 p = 0) ∨ (d2895 p = 2 ∧ d3673 p = 0) ∨ (d2895 p = 2 ∧ d3673 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1258 p pair.1
    have afterEq := eqIntro2078 p pair.2
    have combined := andIntro2197 p beforeEq guard
    have complete := andIntro2012 p afterEq combined
    have bound := compare2056 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro2078 p pair.2
    have combined := andIntro2218 p beforeEq guard
    have complete := andIntro2061 p afterEq combined
    have bound := compare2057 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro2106 p pair.2
    have combined := andIntro2218 p beforeEq guard
    have complete := andIntro2089 p afterEq combined
    have bound := compare2056 p complete
    omega
theorem local56 (p : Pattern) (guard : d62934 p = 1)
    (decreasing : bonus 71 (HazardPattern.afterPattern 10000 p (.walk 71)) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 71) + NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 71))) + bonus 71 (HazardPattern.afterPattern 10000 p (.walk 71)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 71) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) < bonus 49 p at decreasing
  rw [gammaAfter56, at49] at decreasing
  have numeric := numeric56 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71))
  rw [oldBefore49, at49, literal, oldAfter56, gammaAfter56]
  exact numeric
theorem numeric57 (p : Pattern) (guard : d62939 p = 1) (decreasing : d63284 p < d2895 p) :
    d48083 p + d2895 p ≤ (0 : Int) + d47700 p + d63284 p := by
  have beforeRange := bonus_range 49 p
  rw [at49] at beforeRange
  have afterRange := bonus_range 71 (HazardPattern.afterPattern 10000 p (.push 71 (.stay 93)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 71 (.stay 93))) (HazardPattern.afterPattern 10000 p (.push 71 (.stay 93))) ∧ bonus (HazardPattern.nextHero (.push 71 (.stay 93))) (HazardPattern.afterPattern 10000 p (.push 71 (.stay 93))) ≤ 2 at afterRange
  rw [gammaAfter57] at afterRange
  have possibilities : (d2895 p = 1 ∧ d63284 p = 0) ∨ (d2895 p = 2 ∧ d63284 p = 0) ∨ (d2895 p = 2 ∧ d63284 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1258 p pair.1
    have afterEq := eqIntro2223 p pair.2
    have combined := andIntro2324 p beforeEq guard
    have complete := andIntro2408 p afterEq combined
    have bound := compare2058 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro2223 p pair.2
    have combined := andIntro2429 p beforeEq guard
    have complete := andIntro2457 p afterEq combined
    have bound := compare2059 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro2263 p pair.2
    have combined := andIntro2429 p beforeEq guard
    have complete := andIntro2485 p combined afterEq
    have bound := compare2058 p complete
    omega
theorem local57 (p : Pattern) (guard : d62939 p = 1)
    (decreasing : bonus 71 (HazardPattern.afterPattern 10000 p (.push 71 (.stay 93))) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 71 (.stay 93)) + NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 71 (.stay 93)))) + bonus 71 (HazardPattern.afterPattern 10000 p (.push 71 (.stay 93))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 71 (.stay 93)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 71 (.stay 93))) (HazardPattern.afterPattern 10000 p (.push 71 (.stay 93))) < bonus 49 p at decreasing
  rw [gammaAfter57, at49] at decreasing
  have numeric := numeric57 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 71 (.stay 93))) (HazardPattern.afterPattern 10000 p (.push 71 (.stay 93)))
  rw [oldBefore49, at49, literal, oldAfter57, gammaAfter57]
  exact numeric
theorem numeric58 (p : Pattern) (guard : d55755 p = 1) (decreasing : d3015 p < d2895 p) :
    d48083 p + d2895 p ≤ (0 : Int) + d47911 p + d3015 p := by
  have beforeRange := bonus_range 49 p
  rw [at49] at beforeRange
  have afterRange := bonus_range 50 (HazardPattern.afterPattern 10000 p (.walk 50))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ∧ bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) ≤ 2 at afterRange
  rw [gammaAfter58] at afterRange
  have possibilities : (d2895 p = 1 ∧ d3015 p = 0) ∨ (d2895 p = 2 ∧ d3015 p = 0) ∨ (d2895 p = 2 ∧ d3015 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1258 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro2507 p beforeEq guard
    have complete := andIntro2528 p afterEq combined
    have bound := compare2054 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro1405 p pair.2
    have combined := andIntro2549 p beforeEq guard
    have complete := andIntro834 p combined afterEq
    have bound := compare2055 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro1406 p pair.2
    have combined := andIntro2549 p beforeEq guard
    have complete := andIntro835 p combined afterEq
    have bound := compare2054 p complete
    omega
theorem local58 (p : Pattern) (guard : d55755 p = 1)
    (decreasing : bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 50) + NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 50))) + bonus 50 (HazardPattern.afterPattern 10000 p (.walk 50)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 50) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50)) < bonus 49 p at decreasing
  rw [gammaAfter58, at49] at decreasing
  have numeric := numeric58 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 50)) (HazardPattern.afterPattern 10000 p (.walk 50))
  rw [oldBefore49, at49, literal, oldAfter58, gammaAfter58]
  exact numeric
theorem numeric59 (p : Pattern) (guard : d64189 p = 1) (decreasing : d64302 p < d2895 p) :
    d48083 p + d2895 p ≤ (1 : Int) + d47911 p + d64302 p := by
  have beforeRange := bonus_range 49 p
  rw [at49] at beforeRange
  have afterRange := bonus_range 50 (HazardPattern.afterPattern 10000 p (.push 50 (.stay 51)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 50 (.stay 51))) (HazardPattern.afterPattern 10000 p (.push 50 (.stay 51))) ∧ bonus (HazardPattern.nextHero (.push 50 (.stay 51))) (HazardPattern.afterPattern 10000 p (.push 50 (.stay 51))) ≤ 2 at afterRange
  rw [gammaAfter59] at afterRange
  have possibilities : (d2895 p = 1 ∧ d64302 p = 0) ∨ (d2895 p = 2 ∧ d64302 p = 0) ∨ (d2895 p = 2 ∧ d64302 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1258 p pair.1
    have afterEq := eqIntro2284 p pair.2
    have combined := andIntro2570 p beforeEq guard
    have complete := andIntro2571 p afterEq combined
    have bound := compare2189 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro2284 p pair.2
    have combined := andIntro2572 p beforeEq guard
    have complete := andIntro2593 p combined afterEq
    have bound := compare2054 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro2285 p pair.2
    have combined := andIntro2572 p beforeEq guard
    have complete := andIntro2594 p combined afterEq
    have bound := compare2309 p complete
    omega
theorem local59 (p : Pattern) (guard : d64189 p = 1)
    (decreasing : bonus 50 (HazardPattern.afterPattern 10000 p (.push 50 (.stay 51))) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 50 (.stay 51)) + NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 50 (.stay 51)))) + bonus 50 (HazardPattern.afterPattern 10000 p (.push 50 (.stay 51))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 50 (.stay 51)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 50 (.stay 51))) (HazardPattern.afterPattern 10000 p (.push 50 (.stay 51))) < bonus 49 p at decreasing
  rw [gammaAfter59, at49] at decreasing
  have numeric := numeric59 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 50 (.stay 51))) (HazardPattern.afterPattern 10000 p (.push 50 (.stay 51)))
  rw [oldBefore49, at49, literal, oldAfter59, gammaAfter59]
  exact numeric
theorem numeric60 (p : Pattern) (guard : d55878 p = 1) (decreasing : d2782 p < d2895 p) :
    d48083 p + d2895 p ≤ (0 : Int) + d48080 p + d2782 p := by
  have beforeRange := bonus_range 49 p
  rw [at49] at beforeRange
  have afterRange := bonus_range 48 (HazardPattern.afterPattern 10000 p (.walk 48))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ∧ bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) ≤ 2 at afterRange
  rw [gammaAfter60] at afterRange
  have possibilities : (d2895 p = 1 ∧ d2782 p = 0) ∨ (d2895 p = 2 ∧ d2782 p = 0) ∨ (d2895 p = 2 ∧ d2782 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1258 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro2595 p beforeEq guard
    have complete := andIntro878 p afterEq combined
    have bound := compare2310 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro1145 p pair.2
    have combined := andIntro2596 p beforeEq guard
    have complete := andIntro900 p afterEq combined
    have bound := compare2311 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro1166 p pair.2
    have combined := andIntro2596 p beforeEq guard
    have complete := andIntro921 p afterEq combined
    have bound := compare2310 p complete
    omega
theorem local60 (p : Pattern) (guard : d55878 p = 1)
    (decreasing : bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 48) + NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 48))) + bonus 48 (HazardPattern.afterPattern 10000 p (.walk 48)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 48) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48)) < bonus 49 p at decreasing
  rw [gammaAfter60, at49] at decreasing
  have numeric := numeric60 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 48)) (HazardPattern.afterPattern 10000 p (.walk 48))
  rw [oldBefore49, at49, literal, oldAfter60, gammaAfter60]
  exact numeric
theorem numeric61 (p : Pattern) (guard : d60241 p = 1) (decreasing : d0 p < d2895 p) :
    d48083 p + d2895 p ≤ (1 : Int) + d47768 p + d0 p := by
  have beforeRange := bonus_range 49 p
  rw [at49] at beforeRange
  have afterRange := bonus_range 48 (HazardPattern.afterPattern 10000 p (.push 48 (.stay 47)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 48 (.stay 47))) (HazardPattern.afterPattern 10000 p (.push 48 (.stay 47))) ∧ bonus (HazardPattern.nextHero (.push 48 (.stay 47))) (HazardPattern.afterPattern 10000 p (.push 48 (.stay 47))) ≤ 2 at afterRange
  rw [gammaAfter61] at afterRange
  have possibilities : (d2895 p = 1 ∧ d0 p = 0) ∨ (d2895 p = 2 ∧ d0 p = 0) ∨ (d2895 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1258 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro2618 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare2312 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro2639 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare2313 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro2639 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2312 p complete
    omega
theorem local61 (p : Pattern) (guard : d60241 p = 1)
    (decreasing : bonus 48 (HazardPattern.afterPattern 10000 p (.push 48 (.stay 47))) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 48 (.stay 47)) + NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 48 (.stay 47)))) + bonus 48 (HazardPattern.afterPattern 10000 p (.push 48 (.stay 47))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 48 (.stay 47)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 48 (.stay 47))) (HazardPattern.afterPattern 10000 p (.push 48 (.stay 47))) < bonus 49 p at decreasing
  rw [gammaAfter61, at49] at decreasing
  have numeric := numeric61 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 48 (.stay 47))) (HazardPattern.afterPattern 10000 p (.push 48 (.stay 47)))
  rw [oldBefore49, at49, literal, oldAfter61, gammaAfter61]
  exact numeric
theorem numeric62 (p : Pattern) (guard : d56147 p = 1) (decreasing : d2671 p < d2895 p) :
    d48083 p + d2895 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 49 p
  rw [at49] at beforeRange
  have afterRange := bonus_range 28 (HazardPattern.afterPattern 10000 p (.walk 28))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) ∧ bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) ≤ 2 at afterRange
  rw [gammaAfter62] at afterRange
  have possibilities : (d2895 p = 1 ∧ d2671 p = 0) ∨ (d2895 p = 2 ∧ d2671 p = 0) ∨ (d2895 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1258 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro2640 p beforeEq guard
    have complete := andIntro1911 p combined afterEq
    have bound := compare2054 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro1014 p beforeEq guard
    have complete := andIntro744 p combined afterEq
    have bound := compare2055 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro1014 p beforeEq guard
    have complete := andIntro765 p afterEq combined
    have bound := compare2054 p complete
    omega
theorem local62 (p : Pattern) (guard : d56147 p = 1)
    (decreasing : bonus 28 (HazardPattern.afterPattern 10000 p (.walk 28)) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 28) + NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 28))) + bonus 28 (HazardPattern.afterPattern 10000 p (.walk 28)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 28) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) < bonus 49 p at decreasing
  rw [gammaAfter62, at49] at decreasing
  have numeric := numeric62 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28))
  rw [oldBefore49, at49, literal, oldAfter62, gammaAfter62]
  exact numeric
theorem numeric63 (p : Pattern) (guard : d64542 p = 1) (decreasing : d3496 p < d2895 p) :
    d48083 p + d2895 p ≤ (0 : Int) + d47866 p + d3496 p := by
  have beforeRange := bonus_range 49 p
  rw [at49] at beforeRange
  have afterRange := bonus_range 70 (HazardPattern.afterPattern 10000 p (.walk 70))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ∧ bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) ≤ 2 at afterRange
  rw [gammaAfter63] at afterRange
  have possibilities : (d2895 p = 1 ∧ d3496 p = 0) ∨ (d2895 p = 2 ∧ d3496 p = 0) ∨ (d2895 p = 2 ∧ d3496 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1258 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro2662 p beforeEq guard
    have complete := andIntro1535 p afterEq combined
    have bound := compare2314 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro1957 p pair.2
    have combined := andIntro2683 p beforeEq guard
    have complete := andIntro1577 p afterEq combined
    have bound := compare2315 p complete
    omega
  · have beforeEq := eqIntro2127 p pair.1
    have afterEq := eqIntro1978 p pair.2
    have combined := andIntro2683 p beforeEq guard
    have complete := andIntro1598 p afterEq combined
    have bound := compare2314 p complete
    omega
theorem local63 (p : Pattern) (guard : d64542 p = 1)
    (decreasing : bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 70) + NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 70))) + bonus 70 (HazardPattern.afterPattern 10000 p (.walk 70)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 70) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) < bonus 49 p at decreasing
  rw [gammaAfter63, at49] at decreasing
  have numeric := numeric63 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70))
  rw [oldBefore49, at49, literal, oldAfter63, gammaAfter63]
  exact numeric
theorem numeric64 (p : Pattern) (guard : d55880 p = 1) (decreasing : d2671 p < d3015 p) :
    d47911 p + d3015 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 50 p
  rw [at50] at beforeRange
  have afterRange := bonus_range 28 (HazardPattern.afterPattern 10000 p (.walk 28))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) ∧ bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) ≤ 2 at afterRange
  rw [gammaAfter64] at afterRange
  have possibilities : (d3015 p = 1 ∧ d2671 p = 0) ∨ (d3015 p = 2 ∧ d2671 p = 0) ∨ (d3015 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1406 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro2684 p beforeEq guard
    have complete := andIntro2705 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro2706 p beforeEq guard
    have complete := andIntro2707 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro2706 p beforeEq guard
    have complete := andIntro2708 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local64 (p : Pattern) (guard : d55880 p = 1)
    (decreasing : bonus 28 (HazardPattern.afterPattern 10000 p (.walk 28)) < bonus 50 p) :
    NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 50 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 28) + NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 28))) + bonus 28 (HazardPattern.afterPattern 10000 p (.walk 28)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 28) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28)) < bonus 50 p at decreasing
  rw [gammaAfter64, at50] at decreasing
  have numeric := numeric64 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 28)) (HazardPattern.afterPattern 10000 p (.walk 28))
  rw [oldBefore50, at50, literal, oldAfter64, gammaAfter64]
  exact numeric
theorem numeric65 (p : Pattern) (guard : d55892 p = 1) (decreasing : d3142 p < d3015 p) :
    d47911 p + d3015 p ≤ (0 : Int) + d47911 p + d3142 p := by
  have beforeRange := bonus_range 50 p
  rw [at50] at beforeRange
  have afterRange := bonus_range 51 (HazardPattern.afterPattern 10000 p (.walk 51))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ∧ bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) ≤ 2 at afterRange
  rw [gammaAfter65] at afterRange
  have possibilities : (d3015 p = 1 ∧ d3142 p = 0) ∨ (d3015 p = 2 ∧ d3142 p = 0) ∨ (d3015 p = 2 ∧ d3142 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1406 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro2729 p beforeEq guard
    have complete := andIntro2750 p afterEq combined
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1427 p pair.2
    have combined := andIntro2751 p beforeEq guard
    have complete := andIntro2752 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1448 p pair.2
    have combined := andIntro2751 p beforeEq guard
    have complete := andIntro2753 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local65 (p : Pattern) (guard : d55892 p = 1)
    (decreasing : bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 50 p) :
    NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 50 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 51) + NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 51))) + bonus 51 (HazardPattern.afterPattern 10000 p (.walk 51)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 51) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51)) < bonus 50 p at decreasing
  rw [gammaAfter65, at50] at decreasing
  have numeric := numeric65 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 51)) (HazardPattern.afterPattern 10000 p (.walk 51))
  rw [oldBefore50, at50, literal, oldAfter65, gammaAfter65]
  exact numeric
theorem numeric66 (p : Pattern) (guard : d64664 p = 1) (decreasing : d0 p < d3015 p) :
    d47911 p + d3015 p ≤ (1 : Int) + d47911 p + d0 p := by
  have beforeRange := bonus_range 50 p
  rw [at50] at beforeRange
  have afterRange := bonus_range 51 (HazardPattern.afterPattern 10000 p (.push 51 (.stay 52)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 51 (.stay 52))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 52))) ∧ bonus (HazardPattern.nextHero (.push 51 (.stay 52))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 52))) ≤ 2 at afterRange
  rw [gammaAfter66] at afterRange
  have possibilities : (d3015 p = 1 ∧ d0 p = 0) ∨ (d3015 p = 2 ∧ d0 p = 0) ∨ (d3015 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1406 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro2774 p beforeEq guard
    have complete := andIntro2775 p afterEq combined
    have bound := compare2316 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro2776 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro2776 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare11 p complete
    omega
theorem local66 (p : Pattern) (guard : d64664 p = 1)
    (decreasing : bonus 51 (HazardPattern.afterPattern 10000 p (.push 51 (.stay 52))) < bonus 50 p) :
    NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 50 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 51 (.stay 52)) + NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 51 (.stay 52)))) + bonus 51 (HazardPattern.afterPattern 10000 p (.push 51 (.stay 52))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 51 (.stay 52)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 51 (.stay 52))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 52))) < bonus 50 p at decreasing
  rw [gammaAfter66, at50] at decreasing
  have numeric := numeric66 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 51 (.stay 52))) (HazardPattern.afterPattern 10000 p (.push 51 (.stay 52)))
  rw [oldBefore50, at50, literal, oldAfter66, gammaAfter66]
  exact numeric
theorem numeric67 (p : Pattern) (guard : d55755 p = 1) (decreasing : d2895 p < d3015 p) :
    d47911 p + d3015 p ≤ (0 : Int) + d48083 p + d2895 p := by
  have beforeRange := bonus_range 50 p
  rw [at50] at beforeRange
  have afterRange := bonus_range 49 (HazardPattern.afterPattern 10000 p (.walk 49))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) ∧ bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) ≤ 2 at afterRange
  rw [gammaAfter67] at afterRange
  have possibilities : (d3015 p = 1 ∧ d2895 p = 0) ∨ (d3015 p = 2 ∧ d2895 p = 0) ∨ (d3015 p = 2 ∧ d2895 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1406 p pair.1
    have afterEq := eqIntro1209 p pair.2
    have combined := andIntro2797 p beforeEq guard
    have complete := andIntro2818 p afterEq combined
    have bound := compare5 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1209 p pair.2
    have combined := andIntro2819 p beforeEq guard
    have complete := andIntro2820 p combined afterEq
    have bound := compare6 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1258 p pair.2
    have combined := andIntro2819 p beforeEq guard
    have complete := andIntro2821 p combined afterEq
    have bound := compare5 p complete
    omega
theorem local67 (p : Pattern) (guard : d55755 p = 1)
    (decreasing : bonus 49 (HazardPattern.afterPattern 10000 p (.walk 49)) < bonus 50 p) :
    NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 50 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 49) + NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 49))) + bonus 49 (HazardPattern.afterPattern 10000 p (.walk 49)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 49) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49)) < bonus 50 p at decreasing
  rw [gammaAfter67, at50] at decreasing
  have numeric := numeric67 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 49)) (HazardPattern.afterPattern 10000 p (.walk 49))
  rw [oldBefore50, at50, literal, oldAfter67, gammaAfter67]
  exact numeric
theorem numeric68 (p : Pattern) (guard : d61810 p = 1) (decreasing : d0 p < d3015 p) :
    d47911 p + d3015 p ≤ (1 : Int) + d47700 p + d0 p := by
  have beforeRange := bonus_range 50 p
  rw [at50] at beforeRange
  have afterRange := bonus_range 49 (HazardPattern.afterPattern 10000 p (.push 49 (.stay 48)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 49 (.stay 48))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 48))) ∧ bonus (HazardPattern.nextHero (.push 49 (.stay 48))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 48))) ≤ 2 at afterRange
  rw [gammaAfter68] at afterRange
  have possibilities : (d3015 p = 1 ∧ d0 p = 0) ∨ (d3015 p = 2 ∧ d0 p = 0) ∨ (d3015 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1406 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro2842 p beforeEq guard
    have complete := andIntro2843 p afterEq combined
    have bound := compare2475 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro2844 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare7 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro2844 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare2317 p complete
    omega
theorem local68 (p : Pattern) (guard : d61810 p = 1)
    (decreasing : bonus 49 (HazardPattern.afterPattern 10000 p (.push 49 (.stay 48))) < bonus 50 p) :
    NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 50 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 49 (.stay 48)) + NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 49 (.stay 48)))) + bonus 49 (HazardPattern.afterPattern 10000 p (.push 49 (.stay 48))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 49 (.stay 48)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 49 (.stay 48))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 48))) < bonus 50 p at decreasing
  rw [gammaAfter68, at50] at decreasing
  have numeric := numeric68 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 49 (.stay 48))) (HazardPattern.afterPattern 10000 p (.push 49 (.stay 48)))
  rw [oldBefore50, at50, literal, oldAfter68, gammaAfter68]
  exact numeric
theorem numeric69 (p : Pattern) (guard : d56770 p = 1) (decreasing : d2671 p < d3015 p) :
    d47911 p + d3015 p ≤ (0 : Int) + d47911 p + d2671 p := by
  have beforeRange := bonus_range 50 p
  rw [at50] at beforeRange
  have afterRange := bonus_range 29 (HazardPattern.afterPattern 10000 p (.walk 29))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) ∧ bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) ≤ 2 at afterRange
  rw [gammaAfter69] at afterRange
  have possibilities : (d3015 p = 1 ∧ d2671 p = 0) ∨ (d3015 p = 2 ∧ d2671 p = 0) ∨ (d3015 p = 2 ∧ d2671 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1406 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro2845 p beforeEq guard
    have complete := andIntro2705 p combined afterEq
    have bound := compare9 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1382 p pair.2
    have combined := andIntro2846 p beforeEq guard
    have complete := andIntro2707 p combined afterEq
    have bound := compare10 p complete
    omega
  · have beforeEq := eqIntro2306 p pair.1
    have afterEq := eqIntro1187 p pair.2
    have combined := andIntro2846 p beforeEq guard
    have complete := andIntro2708 p combined afterEq
    have bound := compare9 p complete
    omega
theorem local69 (p : Pattern) (guard : d56770 p = 1)
    (decreasing : bonus 29 (HazardPattern.afterPattern 10000 p (.walk 29)) < bonus 50 p) :
    NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 50 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 29) + NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 29))) + bonus 29 (HazardPattern.afterPattern 10000 p (.walk 29)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 29) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29)) < bonus 50 p at decreasing
  rw [gammaAfter69, at50] at decreasing
  have numeric := numeric69 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 29)) (HazardPattern.afterPattern 10000 p (.walk 29))
  rw [oldBefore50, at50, literal, oldAfter69, gammaAfter69]
  exact numeric
end NetHack.Soko22Hazard87
