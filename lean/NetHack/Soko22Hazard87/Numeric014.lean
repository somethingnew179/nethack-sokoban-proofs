import NetHack.Soko22Hazard87.Numeric013
import NetHack.Soko22Hazard87.AndIntroBlocks0433
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric980 (p : Pattern) (guard : d306035 p = 1) (decreasing : d33212 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50101 p + d33212 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 224 (HazardPattern.afterPattern 10000 p (.walk 224))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ∧ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ≤ 2 at afterRange
  rw [gammaAfter980] at afterRange
  have possibilities : (d44879 p = 1 ∧ d33212 p = 0) ∨ (d44879 p = 2 ∧ d33212 p = 0) ∨ (d44879 p = 2 ∧ d33212 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro103291 p guard beforeEq
    have complete := andIntro103627 p afterEq combined
    have bound := compare46642 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro103655 p guard beforeEq
    have complete := andIntro103699 p afterEq combined
    have bound := compare46643 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro24937 p pair.2
    have combined := andIntro103655 p guard beforeEq
    have complete := andIntro103743 p afterEq combined
    have bound := compare46642 p complete
    omega
theorem local980 (p : Pattern) (guard : d306035 p = 1)
    (decreasing : bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 224) + NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 224))) + bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 224) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 247 p at decreasing
  rw [gammaAfter980, at247] at decreasing
  have numeric := numeric980 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224))
  rw [oldBefore247, at247, literal, oldAfter980, gammaAfter980]
  exact numeric
theorem numeric981 (p : Pattern) (guard : d325306 p = 1) (decreasing : d38812 p < d47282 p) :
    d50823 p + d47282 p ≤ (0 : Int) + d50823 p + d38812 p := by
  have beforeRange := bonus_range 248 p
  rw [at248] at beforeRange
  have afterRange := bonus_range 226 (HazardPattern.afterPattern 10000 p (.walk 226))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) ∧ bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) ≤ 2 at afterRange
  rw [gammaAfter981] at afterRange
  have possibilities : (d47282 p = 1 ∧ d38812 p = 0) ∨ (d47282 p = 2 ∧ d38812 p = 0) ∨ (d47282 p = 2 ∧ d38812 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro27657 p pair.2
    have combined := andIntro104012 p beforeEq guard
    have complete := andIntro104350 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro27657 p pair.2
    have combined := andIntro104378 p guard beforeEq
    have complete := andIntro104430 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro27833 p pair.2
    have combined := andIntro104378 p guard beforeEq
    have complete := andIntro104474 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local981 (p : Pattern) (guard : d325306 p = 1)
    (decreasing : bonus 226 (HazardPattern.afterPattern 10000 p (.walk 226)) < bonus 248 p) :
    NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 248 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 226) + NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 226))) + bonus 226 (HazardPattern.afterPattern 10000 p (.walk 226)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 226) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) < bonus 248 p at decreasing
  rw [gammaAfter981, at248] at decreasing
  have numeric := numeric981 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226))
  rw [oldBefore248, at248, literal, oldAfter981, gammaAfter981]
  exact numeric
theorem numeric982 (p : Pattern) (guard : d271212 p = 1) (decreasing : d368769 p < d47282 p) :
    d50823 p + d47282 p ≤ (2 : Int) + d367985 p + d368769 p := by
  have beforeRange := bonus_range 248 p
  rw [at248] at beforeRange
  have afterRange := bonus_range 226 (HazardPattern.afterPattern 10000 p (.push 226 (.stay 204)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 226 (.stay 204))) (HazardPattern.afterPattern 10000 p (.push 226 (.stay 204))) ∧ bonus (HazardPattern.nextHero (.push 226 (.stay 204))) (HazardPattern.afterPattern 10000 p (.push 226 (.stay 204))) ≤ 2 at afterRange
  rw [gammaAfter982] at afterRange
  have possibilities : (d47282 p = 1 ∧ d368769 p = 0) ∨ (d47282 p = 2 ∧ d368769 p = 0) ∨ (d47282 p = 2 ∧ d368769 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro38837 p pair.2
    have combined := andIntro104792 p guard beforeEq
    have complete := andIntro104858 p afterEq combined
    have bound := compare48060 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro38837 p pair.2
    have combined := andIntro104894 p guard beforeEq
    have complete := andIntro104908 p afterEq combined
    have bound := compare48962 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro38899 p pair.2
    have combined := andIntro104894 p guard beforeEq
    have complete := andIntro104922 p combined afterEq
    have bound := compare46644 p complete
    omega
theorem local982 (p : Pattern) (guard : d271212 p = 1)
    (decreasing : bonus 226 (HazardPattern.afterPattern 10000 p (.push 226 (.stay 204))) < bonus 248 p) :
    NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 248 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 226 (.stay 204)) + NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 226 (.stay 204)))) + bonus 226 (HazardPattern.afterPattern 10000 p (.push 226 (.stay 204))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 226 (.stay 204)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 226 (.stay 204))) (HazardPattern.afterPattern 10000 p (.push 226 (.stay 204))) < bonus 248 p at decreasing
  rw [gammaAfter982, at248] at decreasing
  have numeric := numeric982 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 226 (.stay 204))) (HazardPattern.afterPattern 10000 p (.push 226 (.stay 204)))
  rw [oldBefore248, at248, literal, oldAfter982, gammaAfter982]
  exact numeric
theorem numeric983 (p : Pattern) (guard : d370801 p = 1) (decreasing : d47282 p < d47282 p) :
    d50823 p + d47282 p ≤ (0 : Int) + d50823 p + d47282 p := by
  have beforeRange := bonus_range 248 p
  rw [at248] at beforeRange
  have afterRange := bonus_range 249 (HazardPattern.afterPattern 10000 p (.walk 249))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 249)) (HazardPattern.afterPattern 10000 p (.walk 249)) ∧ bonus (HazardPattern.nextHero (.walk 249)) (HazardPattern.afterPattern 10000 p (.walk 249)) ≤ 2 at afterRange
  rw [gammaAfter983] at afterRange
  have possibilities : (d47282 p = 1 ∧ d47282 p = 0) ∨ (d47282 p = 2 ∧ d47282 p = 0) ∨ (d47282 p = 2 ∧ d47282 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro104923 p beforeEq guard
    have complete := andIntro105131 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro105132 p beforeEq guard
    have complete := andIntro105164 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro33595 p pair.2
    have combined := andIntro105132 p beforeEq guard
    have complete := andIntro105196 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local983 (p : Pattern) (guard : d370801 p = 1)
    (decreasing : bonus 249 (HazardPattern.afterPattern 10000 p (.walk 249)) < bonus 248 p) :
    NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 248 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 249) + NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 249))) + bonus 249 (HazardPattern.afterPattern 10000 p (.walk 249)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 249) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 249)) (HazardPattern.afterPattern 10000 p (.walk 249)) < bonus 248 p at decreasing
  rw [gammaAfter983, at248] at decreasing
  have numeric := numeric983 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 249)) (HazardPattern.afterPattern 10000 p (.walk 249))
  rw [oldBefore248, at248, literal, oldAfter983, gammaAfter983]
  exact numeric
theorem numeric984 (p : Pattern) (guard : d370807 p = 1) (decreasing : d370849 p < d47282 p) :
    d50823 p + d47282 p ≤ (0 : Int) + d50823 p + d370849 p := by
  have beforeRange := bonus_range 248 p
  rw [at248] at beforeRange
  have afterRange := bonus_range 249 (HazardPattern.afterPattern 10000 p (.push 249 (.fill 250)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 249 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 249 (.fill 250))) ∧ bonus (HazardPattern.nextHero (.push 249 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 249 (.fill 250))) ≤ 2 at afterRange
  rw [gammaAfter984] at afterRange
  have possibilities : (d47282 p = 1 ∧ d370849 p = 0) ∨ (d47282 p = 2 ∧ d370849 p = 0) ∨ (d47282 p = 2 ∧ d370849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro38907 p pair.2
    have combined := andIntro105202 p beforeEq guard
    have complete := andIntro105203 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro38907 p pair.2
    have combined := andIntro105209 p beforeEq guard
    have complete := andIntro105203 p combined afterEq
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro38915 p pair.2
    have combined := andIntro105209 p beforeEq guard
    have complete := andIntro105210 p combined afterEq
    have bound := compare41207 p complete
    omega
theorem local984 (p : Pattern) (guard : d370807 p = 1)
    (decreasing : bonus 249 (HazardPattern.afterPattern 10000 p (.push 249 (.fill 250))) < bonus 248 p) :
    NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 248 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 249 (.fill 250)) + NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 249 (.fill 250)))) + bonus 249 (HazardPattern.afterPattern 10000 p (.push 249 (.fill 250))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 249 (.fill 250)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 249 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 249 (.fill 250))) < bonus 248 p at decreasing
  rw [gammaAfter984, at248] at decreasing
  have numeric := numeric984 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 249 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 249 (.fill 250)))
  rw [oldBefore248, at248, literal, oldAfter984, gammaAfter984]
  exact numeric
theorem numeric985 (p : Pattern) (guard : d370936 p = 1) (decreasing : d0 p < d47282 p) :
    d50823 p + d47282 p ≤ (0 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 248 p
  rw [at248] at beforeRange
  have afterRange := bonus_range 249 (HazardPattern.afterPattern 10000 p (.push 249 (.stay 250)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 249 (.stay 250))) (HazardPattern.afterPattern 10000 p (.push 249 (.stay 250))) ∧ bonus (HazardPattern.nextHero (.push 249 (.stay 250))) (HazardPattern.afterPattern 10000 p (.push 249 (.stay 250))) ≤ 2 at afterRange
  rw [gammaAfter985] at afterRange
  have possibilities : (d47282 p = 1 ∧ d0 p = 0) ∨ (d47282 p = 2 ∧ d0 p = 0) ∨ (d47282 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro105216 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro105222 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro105222 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare41207 p complete
    omega
theorem local985 (p : Pattern) (guard : d370936 p = 1)
    (decreasing : bonus 249 (HazardPattern.afterPattern 10000 p (.push 249 (.stay 250))) < bonus 248 p) :
    NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 248 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 249 (.stay 250)) + NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 249 (.stay 250)))) + bonus 249 (HazardPattern.afterPattern 10000 p (.push 249 (.stay 250))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 249 (.stay 250)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 249 (.stay 250))) (HazardPattern.afterPattern 10000 p (.push 249 (.stay 250))) < bonus 248 p at decreasing
  rw [gammaAfter985, at248] at decreasing
  have numeric := numeric985 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 249 (.stay 250))) (HazardPattern.afterPattern 10000 p (.push 249 (.stay 250)))
  rw [oldBefore248, at248, literal, oldAfter985, gammaAfter985]
  exact numeric
theorem numeric986 (p : Pattern) (guard : d14 p = 1) (decreasing : d44879 p < d47282 p) :
    d50823 p + d47282 p ≤ (0 : Int) + d51635 p + d44879 p := by
  have beforeRange := bonus_range 248 p
  rw [at248] at beforeRange
  have afterRange := bonus_range 247 (HazardPattern.afterPattern 10000 p (.walk 247))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) ∧ bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) ≤ 2 at afterRange
  rw [gammaAfter986] at afterRange
  have possibilities : (d47282 p = 1 ∧ d44879 p = 0) ∨ (d47282 p = 2 ∧ d44879 p = 0) ∨ (d47282 p = 2 ∧ d44879 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro31994 p pair.2
    have combined := andIntro105483 p guard beforeEq
    have complete := andIntro105763 p afterEq combined
    have bound := compare41213 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro31994 p pair.2
    have combined := andIntro105796 p guard beforeEq
    have complete := andIntro105834 p afterEq combined
    have bound := compare41214 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro32161 p pair.2
    have combined := andIntro105796 p guard beforeEq
    have complete := andIntro105872 p afterEq combined
    have bound := compare41213 p complete
    omega
theorem local986 (p : Pattern) (guard : d14 p = 1)
    (decreasing : bonus 247 (HazardPattern.afterPattern 10000 p (.walk 247)) < bonus 248 p) :
    NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 248 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 247) + NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 247))) + bonus 247 (HazardPattern.afterPattern 10000 p (.walk 247)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 247) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) < bonus 248 p at decreasing
  rw [gammaAfter986, at248] at decreasing
  have numeric := numeric986 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247))
  rw [oldBefore248, at248, literal, oldAfter986, gammaAfter986]
  exact numeric
theorem numeric987 (p : Pattern) (guard : d46864 p = 1) (decreasing : d373063 p < d47282 p) :
    d50823 p + d47282 p ≤ (2 : Int) + d371353 p + d373063 p := by
  have beforeRange := bonus_range 248 p
  rw [at248] at beforeRange
  have afterRange := bonus_range 247 (HazardPattern.afterPattern 10000 p (.push 247 (.stay 246)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 247 (.stay 246))) (HazardPattern.afterPattern 10000 p (.push 247 (.stay 246))) ∧ bonus (HazardPattern.nextHero (.push 247 (.stay 246))) (HazardPattern.afterPattern 10000 p (.push 247 (.stay 246))) ≤ 2 at afterRange
  rw [gammaAfter987] at afterRange
  have possibilities : (d47282 p = 1 ∧ d373063 p = 0) ∨ (d47282 p = 2 ∧ d373063 p = 0) ∨ (d47282 p = 2 ∧ d373063 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro39211 p pair.2
    have combined := andIntro106146 p guard beforeEq
    have complete := andIntro106321 p afterEq combined
    have bound := compare49459 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro39211 p pair.2
    have combined := andIntro106349 p guard beforeEq
    have complete := andIntro106381 p afterEq combined
    have bound := compare49828 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro39323 p pair.2
    have combined := andIntro106349 p guard beforeEq
    have complete := andIntro106419 p combined afterEq
    have bound := compare48963 p complete
    omega
theorem local987 (p : Pattern) (guard : d46864 p = 1)
    (decreasing : bonus 247 (HazardPattern.afterPattern 10000 p (.push 247 (.stay 246))) < bonus 248 p) :
    NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 248 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 247 (.stay 246)) + NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 247 (.stay 246)))) + bonus 247 (HazardPattern.afterPattern 10000 p (.push 247 (.stay 246))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 247 (.stay 246)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 247 (.stay 246))) (HazardPattern.afterPattern 10000 p (.push 247 (.stay 246))) < bonus 248 p at decreasing
  rw [gammaAfter987, at248] at decreasing
  have numeric := numeric987 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 247 (.stay 246))) (HazardPattern.afterPattern 10000 p (.push 247 (.stay 246)))
  rw [oldBefore248, at248, literal, oldAfter987, gammaAfter987]
  exact numeric
theorem numeric988 (p : Pattern) (guard : d318725 p = 1) (decreasing : d36004 p < d47282 p) :
    d50823 p + d47282 p ≤ (0 : Int) + d50493 p + d36004 p := by
  have beforeRange := bonus_range 248 p
  rw [at248] at beforeRange
  have afterRange := bonus_range 225 (HazardPattern.afterPattern 10000 p (.walk 225))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ∧ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ≤ 2 at afterRange
  rw [gammaAfter988] at afterRange
  have possibilities : (d47282 p = 1 ∧ d36004 p = 0) ∨ (d47282 p = 2 ∧ d36004 p = 0) ∨ (d47282 p = 2 ∧ d36004 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro106632 p guard beforeEq
    have complete := andIntro106963 p afterEq combined
    have bound := compare41209 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro106995 p guard beforeEq
    have complete := andIntro107045 p afterEq combined
    have bound := compare41210 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro26978 p pair.2
    have combined := andIntro106995 p guard beforeEq
    have complete := andIntro107089 p afterEq combined
    have bound := compare41209 p complete
    omega
theorem local988 (p : Pattern) (guard : d318725 p = 1)
    (decreasing : bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 248 p) :
    NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 248 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 225) + NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 225))) + bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 225) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 248 p at decreasing
  rw [gammaAfter988, at248] at decreasing
  have numeric := numeric988 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225))
  rw [oldBefore248, at248, literal, oldAfter988, gammaAfter988]
  exact numeric
theorem numeric989 (p : Pattern) (guard : d375596 p = 1) (decreasing : d47326 p < d47282 p) :
    d50823 p + d47282 p ≤ (0 : Int) + d50823 p + d47326 p := by
  have beforeRange := bonus_range 249 p
  rw [at249] at beforeRange
  have afterRange := bonus_range 250 (HazardPattern.afterPattern 10000 p (.walk 250))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 250)) (HazardPattern.afterPattern 10000 p (.walk 250)) ∧ bonus (HazardPattern.nextHero (.walk 250)) (HazardPattern.afterPattern 10000 p (.walk 250)) ≤ 2 at afterRange
  rw [gammaAfter989] at afterRange
  have possibilities : (d47282 p = 1 ∧ d47326 p = 0) ∨ (d47282 p = 2 ∧ d47326 p = 0) ∨ (d47282 p = 2 ∧ d47326 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro39331 p pair.2
    have combined := andIntro107097 p beforeEq guard
    have complete := andIntro107105 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro39331 p pair.2
    have combined := andIntro107113 p beforeEq guard
    have complete := andIntro107121 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro39339 p pair.2
    have combined := andIntro107113 p beforeEq guard
    have complete := andIntro107129 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local989 (p : Pattern) (guard : d375596 p = 1)
    (decreasing : bonus 250 (HazardPattern.afterPattern 10000 p (.walk 250)) < bonus 249 p) :
    NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 249 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 250) + NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 250))) + bonus 250 (HazardPattern.afterPattern 10000 p (.walk 250)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 250) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 250)) (HazardPattern.afterPattern 10000 p (.walk 250)) < bonus 249 p at decreasing
  rw [gammaAfter989, at249] at decreasing
  have numeric := numeric989 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 250)) (HazardPattern.afterPattern 10000 p (.walk 250))
  rw [oldBefore249, at249, literal, oldAfter989, gammaAfter989]
  exact numeric
theorem numeric990 (p : Pattern) (guard : d375734 p = 1) (decreasing : d375777 p < d47282 p) :
    d50823 p + d47282 p ≤ (1 : Int) + d50823 p + d375777 p := by
  have beforeRange := bonus_range 249 p
  rw [at249] at beforeRange
  have afterRange := bonus_range 250 (HazardPattern.afterPattern 10000 p (.push 250 (.fill 251)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 250 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 250 (.fill 251))) ∧ bonus (HazardPattern.nextHero (.push 250 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 250 (.fill 251))) ≤ 2 at afterRange
  rw [gammaAfter990] at afterRange
  have possibilities : (d47282 p = 1 ∧ d375777 p = 0) ∨ (d47282 p = 2 ∧ d375777 p = 0) ∨ (d47282 p = 2 ∧ d375777 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro39347 p pair.2
    have combined := andIntro107135 p beforeEq guard
    have complete := andIntro107136 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro39347 p pair.2
    have combined := andIntro107142 p beforeEq guard
    have complete := andIntro107136 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro39355 p pair.2
    have combined := andIntro107142 p beforeEq guard
    have complete := andIntro107143 p combined afterEq
    have bound := compare49829 p complete
    omega
theorem local990 (p : Pattern) (guard : d375734 p = 1)
    (decreasing : bonus 250 (HazardPattern.afterPattern 10000 p (.push 250 (.fill 251))) < bonus 249 p) :
    NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 249 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 250 (.fill 251)) + NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 250 (.fill 251)))) + bonus 250 (HazardPattern.afterPattern 10000 p (.push 250 (.fill 251))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 250 (.fill 251)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 250 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 250 (.fill 251))) < bonus 249 p at decreasing
  rw [gammaAfter990, at249] at decreasing
  have numeric := numeric990 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 250 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 250 (.fill 251)))
  rw [oldBefore249, at249, literal, oldAfter990, gammaAfter990]
  exact numeric
theorem numeric991 (p : Pattern) (guard : d375866 p = 1) (decreasing : d0 p < d47282 p) :
    d50823 p + d47282 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 249 p
  rw [at249] at beforeRange
  have afterRange := bonus_range 250 (HazardPattern.afterPattern 10000 p (.push 250 (.stay 251)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 250 (.stay 251))) (HazardPattern.afterPattern 10000 p (.push 250 (.stay 251))) ∧ bonus (HazardPattern.nextHero (.push 250 (.stay 251))) (HazardPattern.afterPattern 10000 p (.push 250 (.stay 251))) ≤ 2 at afterRange
  rw [gammaAfter991] at afterRange
  have possibilities : (d47282 p = 1 ∧ d0 p = 0) ∨ (d47282 p = 2 ∧ d0 p = 0) ∨ (d47282 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107149 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107155 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro107155 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local991 (p : Pattern) (guard : d375866 p = 1)
    (decreasing : bonus 250 (HazardPattern.afterPattern 10000 p (.push 250 (.stay 251))) < bonus 249 p) :
    NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 249 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 250 (.stay 251)) + NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 250 (.stay 251)))) + bonus 250 (HazardPattern.afterPattern 10000 p (.push 250 (.stay 251))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 250 (.stay 251)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 250 (.stay 251))) (HazardPattern.afterPattern 10000 p (.push 250 (.stay 251))) < bonus 249 p at decreasing
  rw [gammaAfter991, at249] at decreasing
  have numeric := numeric991 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 250 (.stay 251))) (HazardPattern.afterPattern 10000 p (.push 250 (.stay 251)))
  rw [oldBefore249, at249, literal, oldAfter991, gammaAfter991]
  exact numeric
theorem numeric992 (p : Pattern) (guard : d370801 p = 1) (decreasing : d47282 p < d47282 p) :
    d50823 p + d47282 p ≤ (0 : Int) + d50823 p + d47282 p := by
  have beforeRange := bonus_range 249 p
  rw [at249] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.walk 248))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248)) ∧ bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248)) ≤ 2 at afterRange
  rw [gammaAfter992] at afterRange
  have possibilities : (d47282 p = 1 ∧ d47282 p = 0) ∨ (d47282 p = 2 ∧ d47282 p = 0) ∨ (d47282 p = 2 ∧ d47282 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro104923 p beforeEq guard
    have complete := andIntro105131 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro105132 p beforeEq guard
    have complete := andIntro105164 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro33595 p pair.2
    have combined := andIntro105132 p beforeEq guard
    have complete := andIntro105196 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local992 (p : Pattern) (guard : d370801 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.walk 248)) < bonus 249 p) :
    NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 249 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 248) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 248))) + bonus 248 (HazardPattern.afterPattern 10000 p (.walk 248)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 248) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248)) < bonus 249 p at decreasing
  rw [gammaAfter992, at249] at decreasing
  have numeric := numeric992 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248))
  rw [oldBefore249, at249, literal, oldAfter992, gammaAfter992]
  exact numeric
theorem numeric993 (p : Pattern) (guard : d358929 p = 1) (decreasing : d377673 p < d47282 p) :
    d50823 p + d47282 p ≤ (2 : Int) + d376289 p + d377673 p := by
  have beforeRange := bonus_range 249 p
  rw [at249] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.push 248 (.stay 247)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 248 (.stay 247))) (HazardPattern.afterPattern 10000 p (.push 248 (.stay 247))) ∧ bonus (HazardPattern.nextHero (.push 248 (.stay 247))) (HazardPattern.afterPattern 10000 p (.push 248 (.stay 247))) ≤ 2 at afterRange
  rw [gammaAfter993] at afterRange
  have possibilities : (d47282 p = 1 ∧ d377673 p = 0) ∨ (d47282 p = 2 ∧ d377673 p = 0) ∨ (d47282 p = 2 ∧ d377673 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro39615 p pair.2
    have combined := andIntro107477 p beforeEq guard
    have complete := andIntro107478 p combined afterEq
    have bound := compare49830 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro39615 p pair.2
    have combined := andIntro107515 p guard beforeEq
    have complete := andIntro107478 p combined afterEq
    have bound := compare49831 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro39718 p pair.2
    have combined := andIntro107515 p guard beforeEq
    have complete := andIntro107516 p combined afterEq
    have bound := compare49830 p complete
    omega
theorem local993 (p : Pattern) (guard : d358929 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.stay 247))) < bonus 249 p) :
    NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 249 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 248 (.stay 247)) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.stay 247)))) + bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.stay 247))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 248 (.stay 247)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 248 (.stay 247))) (HazardPattern.afterPattern 10000 p (.push 248 (.stay 247))) < bonus 249 p at decreasing
  rw [gammaAfter993, at249] at decreasing
  have numeric := numeric993 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 248 (.stay 247))) (HazardPattern.afterPattern 10000 p (.push 248 (.stay 247)))
  rw [oldBefore249, at249, literal, oldAfter993, gammaAfter993]
  exact numeric
theorem numeric994 (p : Pattern) (guard : d331330 p = 1) (decreasing : d38812 p < d47282 p) :
    d50823 p + d47282 p ≤ (0 : Int) + d50823 p + d38812 p := by
  have beforeRange := bonus_range 249 p
  rw [at249] at beforeRange
  have afterRange := bonus_range 226 (HazardPattern.afterPattern 10000 p (.walk 226))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) ∧ bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) ≤ 2 at afterRange
  rw [gammaAfter994] at afterRange
  have possibilities : (d47282 p = 1 ∧ d38812 p = 0) ∨ (d47282 p = 2 ∧ d38812 p = 0) ∨ (d47282 p = 2 ∧ d38812 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro33595 p pair.1
    have afterEq := eqIntro27657 p pair.2
    have combined := andIntro107522 p beforeEq guard
    have complete := andIntro104350 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro27657 p pair.2
    have combined := andIntro107528 p guard beforeEq
    have complete := andIntro104430 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro38675 p pair.1
    have afterEq := eqIntro27833 p pair.2
    have combined := andIntro107528 p guard beforeEq
    have complete := andIntro104474 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local994 (p : Pattern) (guard : d331330 p = 1)
    (decreasing : bonus 226 (HazardPattern.afterPattern 10000 p (.walk 226)) < bonus 249 p) :
    NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 249 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 226) + NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 226))) + bonus 226 (HazardPattern.afterPattern 10000 p (.walk 226)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 226) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) < bonus 249 p at decreasing
  rw [gammaAfter994, at249] at decreasing
  have numeric := numeric994 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226))
  rw [oldBefore249, at249, literal, oldAfter994, gammaAfter994]
  exact numeric
theorem numeric995 (p : Pattern) (guard : d378991 p = 1) (decreasing : d47371 p < d47326 p) :
    d50823 p + d47326 p ≤ (0 : Int) + d50823 p + d47371 p := by
  have beforeRange := bonus_range 250 p
  rw [at250] at beforeRange
  have afterRange := bonus_range 251 (HazardPattern.afterPattern 10000 p (.walk 251))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 251)) (HazardPattern.afterPattern 10000 p (.walk 251)) ∧ bonus (HazardPattern.nextHero (.walk 251)) (HazardPattern.afterPattern 10000 p (.walk 251)) ≤ 2 at afterRange
  rw [gammaAfter995] at afterRange
  have possibilities : (d47326 p = 1 ∧ d47371 p = 0) ∨ (d47326 p = 2 ∧ d47371 p = 0) ∨ (d47326 p = 2 ∧ d47371 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39339 p pair.1
    have afterEq := eqIntro39726 p pair.2
    have combined := andIntro107536 p beforeEq guard
    have complete := andIntro107544 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39734 p pair.1
    have afterEq := eqIntro39726 p pair.2
    have combined := andIntro107552 p beforeEq guard
    have complete := andIntro107560 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro39734 p pair.1
    have afterEq := eqIntro39742 p pair.2
    have combined := andIntro107552 p beforeEq guard
    have complete := andIntro107568 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local995 (p : Pattern) (guard : d378991 p = 1)
    (decreasing : bonus 251 (HazardPattern.afterPattern 10000 p (.walk 251)) < bonus 250 p) :
    NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 250 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 251) + NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 251))) + bonus 251 (HazardPattern.afterPattern 10000 p (.walk 251)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 251) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 251)) (HazardPattern.afterPattern 10000 p (.walk 251)) < bonus 250 p at decreasing
  rw [gammaAfter995, at250] at decreasing
  have numeric := numeric995 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 251)) (HazardPattern.afterPattern 10000 p (.walk 251))
  rw [oldBefore250, at250, literal, oldAfter995, gammaAfter995]
  exact numeric
theorem numeric996 (p : Pattern) (guard : d379135 p = 1) (decreasing : d379179 p < d47326 p) :
    d50823 p + d47326 p ≤ (1 : Int) + d50823 p + d379179 p := by
  have beforeRange := bonus_range 250 p
  rw [at250] at beforeRange
  have afterRange := bonus_range 251 (HazardPattern.afterPattern 10000 p (.push 251 (.fill 252)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 251 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 251 (.fill 252))) ∧ bonus (HazardPattern.nextHero (.push 251 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 251 (.fill 252))) ≤ 2 at afterRange
  rw [gammaAfter996] at afterRange
  have possibilities : (d47326 p = 1 ∧ d379179 p = 0) ∨ (d47326 p = 2 ∧ d379179 p = 0) ∨ (d47326 p = 2 ∧ d379179 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39339 p pair.1
    have afterEq := eqIntro39750 p pair.2
    have combined := andIntro107574 p beforeEq guard
    have complete := andIntro107575 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39734 p pair.1
    have afterEq := eqIntro39750 p pair.2
    have combined := andIntro107581 p beforeEq guard
    have complete := andIntro107575 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39734 p pair.1
    have afterEq := eqIntro39758 p pair.2
    have combined := andIntro107581 p beforeEq guard
    have complete := andIntro107582 p combined afterEq
    have bound := compare49829 p complete
    omega
theorem local996 (p : Pattern) (guard : d379135 p = 1)
    (decreasing : bonus 251 (HazardPattern.afterPattern 10000 p (.push 251 (.fill 252))) < bonus 250 p) :
    NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 250 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 251 (.fill 252)) + NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 251 (.fill 252)))) + bonus 251 (HazardPattern.afterPattern 10000 p (.push 251 (.fill 252))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 251 (.fill 252)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 251 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 251 (.fill 252))) < bonus 250 p at decreasing
  rw [gammaAfter996, at250] at decreasing
  have numeric := numeric996 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 251 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 251 (.fill 252)))
  rw [oldBefore250, at250, literal, oldAfter996, gammaAfter996]
  exact numeric
theorem numeric997 (p : Pattern) (guard : d379271 p = 1) (decreasing : d0 p < d47326 p) :
    d50823 p + d47326 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 250 p
  rw [at250] at beforeRange
  have afterRange := bonus_range 251 (HazardPattern.afterPattern 10000 p (.push 251 (.stay 252)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 251 (.stay 252))) (HazardPattern.afterPattern 10000 p (.push 251 (.stay 252))) ∧ bonus (HazardPattern.nextHero (.push 251 (.stay 252))) (HazardPattern.afterPattern 10000 p (.push 251 (.stay 252))) ≤ 2 at afterRange
  rw [gammaAfter997] at afterRange
  have possibilities : (d47326 p = 1 ∧ d0 p = 0) ∨ (d47326 p = 2 ∧ d0 p = 0) ∨ (d47326 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39339 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107588 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39734 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107594 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39734 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro107594 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local997 (p : Pattern) (guard : d379271 p = 1)
    (decreasing : bonus 251 (HazardPattern.afterPattern 10000 p (.push 251 (.stay 252))) < bonus 250 p) :
    NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 250 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 251 (.stay 252)) + NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 251 (.stay 252)))) + bonus 251 (HazardPattern.afterPattern 10000 p (.push 251 (.stay 252))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 251 (.stay 252)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 251 (.stay 252))) (HazardPattern.afterPattern 10000 p (.push 251 (.stay 252))) < bonus 250 p at decreasing
  rw [gammaAfter997, at250] at decreasing
  have numeric := numeric997 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 251 (.stay 252))) (HazardPattern.afterPattern 10000 p (.push 251 (.stay 252)))
  rw [oldBefore250, at250, literal, oldAfter997, gammaAfter997]
  exact numeric
theorem numeric998 (p : Pattern) (guard : d375596 p = 1) (decreasing : d47282 p < d47326 p) :
    d50823 p + d47326 p ≤ (0 : Int) + d50823 p + d47282 p := by
  have beforeRange := bonus_range 250 p
  rw [at250] at beforeRange
  have afterRange := bonus_range 249 (HazardPattern.afterPattern 10000 p (.walk 249))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 249)) (HazardPattern.afterPattern 10000 p (.walk 249)) ∧ bonus (HazardPattern.nextHero (.walk 249)) (HazardPattern.afterPattern 10000 p (.walk 249)) ≤ 2 at afterRange
  rw [gammaAfter998] at afterRange
  have possibilities : (d47326 p = 1 ∧ d47282 p = 0) ∨ (d47326 p = 2 ∧ d47282 p = 0) ∨ (d47326 p = 2 ∧ d47282 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39339 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro107595 p guard beforeEq
    have complete := andIntro107603 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39734 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro107604 p guard beforeEq
    have complete := andIntro107612 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro39734 p pair.1
    have afterEq := eqIntro33595 p pair.2
    have combined := andIntro107604 p guard beforeEq
    have complete := andIntro107620 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local998 (p : Pattern) (guard : d375596 p = 1)
    (decreasing : bonus 249 (HazardPattern.afterPattern 10000 p (.walk 249)) < bonus 250 p) :
    NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 250 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 249) + NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 249))) + bonus 249 (HazardPattern.afterPattern 10000 p (.walk 249)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 249) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 249)) (HazardPattern.afterPattern 10000 p (.walk 249)) < bonus 250 p at decreasing
  rw [gammaAfter998, at250] at decreasing
  have numeric := numeric998 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 249)) (HazardPattern.afterPattern 10000 p (.walk 249))
  rw [oldBefore250, at250, literal, oldAfter998, gammaAfter998]
  exact numeric
theorem numeric999 (p : Pattern) (guard : d370936 p = 1) (decreasing : d0 p < d47326 p) :
    d50823 p + d47326 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 250 p
  rw [at250] at beforeRange
  have afterRange := bonus_range 249 (HazardPattern.afterPattern 10000 p (.push 249 (.stay 248)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 249 (.stay 248))) (HazardPattern.afterPattern 10000 p (.push 249 (.stay 248))) ∧ bonus (HazardPattern.nextHero (.push 249 (.stay 248))) (HazardPattern.afterPattern 10000 p (.push 249 (.stay 248))) ≤ 2 at afterRange
  rw [gammaAfter999] at afterRange
  have possibilities : (d47326 p = 1 ∧ d0 p = 0) ∨ (d47326 p = 2 ∧ d0 p = 0) ∨ (d47326 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39339 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107626 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39734 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107632 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39734 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro107632 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local999 (p : Pattern) (guard : d370936 p = 1)
    (decreasing : bonus 249 (HazardPattern.afterPattern 10000 p (.push 249 (.stay 248))) < bonus 250 p) :
    NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 250 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 249 (.stay 248)) + NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 249 (.stay 248)))) + bonus 249 (HazardPattern.afterPattern 10000 p (.push 249 (.stay 248))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 249 (.stay 248)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 249 (.stay 248))) (HazardPattern.afterPattern 10000 p (.push 249 (.stay 248))) < bonus 250 p at decreasing
  rw [gammaAfter999, at250] at decreasing
  have numeric := numeric999 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 249 (.stay 248))) (HazardPattern.afterPattern 10000 p (.push 249 (.stay 248)))
  rw [oldBefore250, at250, literal, oldAfter999, gammaAfter999]
  exact numeric
theorem numeric1000 (p : Pattern) (guard : d379277 p = 1) (decreasing : d47417 p < d47371 p) :
    d50823 p + d47371 p ≤ (0 : Int) + d50823 p + d47417 p := by
  have beforeRange := bonus_range 251 p
  rw [at251] at beforeRange
  have afterRange := bonus_range 252 (HazardPattern.afterPattern 10000 p (.walk 252))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 252)) (HazardPattern.afterPattern 10000 p (.walk 252)) ∧ bonus (HazardPattern.nextHero (.walk 252)) (HazardPattern.afterPattern 10000 p (.walk 252)) ≤ 2 at afterRange
  rw [gammaAfter1000] at afterRange
  have possibilities : (d47371 p = 1 ∧ d47417 p = 0) ∨ (d47371 p = 2 ∧ d47417 p = 0) ∨ (d47371 p = 2 ∧ d47417 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39742 p pair.1
    have afterEq := eqIntro39766 p pair.2
    have combined := andIntro107640 p beforeEq guard
    have complete := andIntro107648 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39774 p pair.1
    have afterEq := eqIntro39766 p pair.2
    have combined := andIntro107656 p beforeEq guard
    have complete := andIntro107664 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro39774 p pair.1
    have afterEq := eqIntro39782 p pair.2
    have combined := andIntro107656 p beforeEq guard
    have complete := andIntro107672 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local1000 (p : Pattern) (guard : d379277 p = 1)
    (decreasing : bonus 252 (HazardPattern.afterPattern 10000 p (.walk 252)) < bonus 251 p) :
    NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 251 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 252) + NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 252))) + bonus 252 (HazardPattern.afterPattern 10000 p (.walk 252)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 252) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 252)) (HazardPattern.afterPattern 10000 p (.walk 252)) < bonus 251 p at decreasing
  rw [gammaAfter1000, at251] at decreasing
  have numeric := numeric1000 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 252)) (HazardPattern.afterPattern 10000 p (.walk 252))
  rw [oldBefore251, at251, literal, oldAfter1000, gammaAfter1000]
  exact numeric
theorem numeric1001 (p : Pattern) (guard : d379424 p = 1) (decreasing : d379469 p < d47371 p) :
    d50823 p + d47371 p ≤ (1 : Int) + d50823 p + d379469 p := by
  have beforeRange := bonus_range 251 p
  rw [at251] at beforeRange
  have afterRange := bonus_range 252 (HazardPattern.afterPattern 10000 p (.push 252 (.fill 253)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 252 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 252 (.fill 253))) ∧ bonus (HazardPattern.nextHero (.push 252 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 252 (.fill 253))) ≤ 2 at afterRange
  rw [gammaAfter1001] at afterRange
  have possibilities : (d47371 p = 1 ∧ d379469 p = 0) ∨ (d47371 p = 2 ∧ d379469 p = 0) ∨ (d47371 p = 2 ∧ d379469 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39742 p pair.1
    have afterEq := eqIntro39790 p pair.2
    have combined := andIntro107678 p beforeEq guard
    have complete := andIntro107679 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39774 p pair.1
    have afterEq := eqIntro39790 p pair.2
    have combined := andIntro107685 p beforeEq guard
    have complete := andIntro107679 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39774 p pair.1
    have afterEq := eqIntro39798 p pair.2
    have combined := andIntro107685 p beforeEq guard
    have complete := andIntro107686 p combined afterEq
    have bound := compare49829 p complete
    omega
theorem local1001 (p : Pattern) (guard : d379424 p = 1)
    (decreasing : bonus 252 (HazardPattern.afterPattern 10000 p (.push 252 (.fill 253))) < bonus 251 p) :
    NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 251 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 252 (.fill 253)) + NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 252 (.fill 253)))) + bonus 252 (HazardPattern.afterPattern 10000 p (.push 252 (.fill 253))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 252 (.fill 253)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 252 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 252 (.fill 253))) < bonus 251 p at decreasing
  rw [gammaAfter1001, at251] at decreasing
  have numeric := numeric1001 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 252 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 252 (.fill 253)))
  rw [oldBefore251, at251, literal, oldAfter1001, gammaAfter1001]
  exact numeric
theorem numeric1002 (p : Pattern) (guard : d379563 p = 1) (decreasing : d0 p < d47371 p) :
    d50823 p + d47371 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 251 p
  rw [at251] at beforeRange
  have afterRange := bonus_range 252 (HazardPattern.afterPattern 10000 p (.push 252 (.stay 253)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 252 (.stay 253))) (HazardPattern.afterPattern 10000 p (.push 252 (.stay 253))) ∧ bonus (HazardPattern.nextHero (.push 252 (.stay 253))) (HazardPattern.afterPattern 10000 p (.push 252 (.stay 253))) ≤ 2 at afterRange
  rw [gammaAfter1002] at afterRange
  have possibilities : (d47371 p = 1 ∧ d0 p = 0) ∨ (d47371 p = 2 ∧ d0 p = 0) ∨ (d47371 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39742 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107692 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39774 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107698 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39774 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro107698 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1002 (p : Pattern) (guard : d379563 p = 1)
    (decreasing : bonus 252 (HazardPattern.afterPattern 10000 p (.push 252 (.stay 253))) < bonus 251 p) :
    NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 251 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 252 (.stay 253)) + NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 252 (.stay 253)))) + bonus 252 (HazardPattern.afterPattern 10000 p (.push 252 (.stay 253))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 252 (.stay 253)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 252 (.stay 253))) (HazardPattern.afterPattern 10000 p (.push 252 (.stay 253))) < bonus 251 p at decreasing
  rw [gammaAfter1002, at251] at decreasing
  have numeric := numeric1002 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 252 (.stay 253))) (HazardPattern.afterPattern 10000 p (.push 252 (.stay 253)))
  rw [oldBefore251, at251, literal, oldAfter1002, gammaAfter1002]
  exact numeric
theorem numeric1003 (p : Pattern) (guard : d378991 p = 1) (decreasing : d47326 p < d47371 p) :
    d50823 p + d47371 p ≤ (0 : Int) + d50823 p + d47326 p := by
  have beforeRange := bonus_range 251 p
  rw [at251] at beforeRange
  have afterRange := bonus_range 250 (HazardPattern.afterPattern 10000 p (.walk 250))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 250)) (HazardPattern.afterPattern 10000 p (.walk 250)) ∧ bonus (HazardPattern.nextHero (.walk 250)) (HazardPattern.afterPattern 10000 p (.walk 250)) ≤ 2 at afterRange
  rw [gammaAfter1003] at afterRange
  have possibilities : (d47371 p = 1 ∧ d47326 p = 0) ∨ (d47371 p = 2 ∧ d47326 p = 0) ∨ (d47371 p = 2 ∧ d47326 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39742 p pair.1
    have afterEq := eqIntro39331 p pair.2
    have combined := andIntro107699 p guard beforeEq
    have complete := andIntro107707 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39774 p pair.1
    have afterEq := eqIntro39331 p pair.2
    have combined := andIntro107708 p guard beforeEq
    have complete := andIntro107716 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro39774 p pair.1
    have afterEq := eqIntro39339 p pair.2
    have combined := andIntro107708 p guard beforeEq
    have complete := andIntro107724 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local1003 (p : Pattern) (guard : d378991 p = 1)
    (decreasing : bonus 250 (HazardPattern.afterPattern 10000 p (.walk 250)) < bonus 251 p) :
    NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 251 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 250) + NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 250))) + bonus 250 (HazardPattern.afterPattern 10000 p (.walk 250)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 250) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 250)) (HazardPattern.afterPattern 10000 p (.walk 250)) < bonus 251 p at decreasing
  rw [gammaAfter1003, at251] at decreasing
  have numeric := numeric1003 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 250)) (HazardPattern.afterPattern 10000 p (.walk 250))
  rw [oldBefore251, at251, literal, oldAfter1003, gammaAfter1003]
  exact numeric
theorem numeric1004 (p : Pattern) (guard : d379577 p = 1) (decreasing : d0 p < d47371 p) :
    d50823 p + d47371 p ≤ (12 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 251 p
  rw [at251] at beforeRange
  have afterRange := bonus_range 250 (HazardPattern.afterPattern 10000 p (.push 250 (.stay 245)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 250 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 250 (.stay 245))) ∧ bonus (HazardPattern.nextHero (.push 250 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 250 (.stay 245))) ≤ 2 at afterRange
  rw [gammaAfter1004] at afterRange
  have possibilities : (d47371 p = 1 ∧ d0 p = 0) ∨ (d47371 p = 2 ∧ d0 p = 0) ∨ (d47371 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39742 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107730 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49832 p complete
    omega
  · have beforeEq := eqIntro39774 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107736 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49833 p complete
    omega
  · have beforeEq := eqIntro39774 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro107736 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49832 p complete
    omega
theorem local1004 (p : Pattern) (guard : d379577 p = 1)
    (decreasing : bonus 250 (HazardPattern.afterPattern 10000 p (.push 250 (.stay 245))) < bonus 251 p) :
    NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 251 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 250 (.stay 245)) + NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 250 (.stay 245)))) + bonus 250 (HazardPattern.afterPattern 10000 p (.push 250 (.stay 245))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 250 (.stay 245)) = (12 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 250 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 250 (.stay 245))) < bonus 251 p at decreasing
  rw [gammaAfter1004, at251] at decreasing
  have numeric := numeric1004 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 250 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 250 (.stay 245)))
  rw [oldBefore251, at251, literal, oldAfter1004, gammaAfter1004]
  exact numeric
theorem numeric1005 (p : Pattern) (guard : d379583 p = 1) (decreasing : d47464 p < d47417 p) :
    d50823 p + d47417 p ≤ (0 : Int) + d50823 p + d47464 p := by
  have beforeRange := bonus_range 252 p
  rw [at252] at beforeRange
  have afterRange := bonus_range 253 (HazardPattern.afterPattern 10000 p (.walk 253))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 253)) (HazardPattern.afterPattern 10000 p (.walk 253)) ∧ bonus (HazardPattern.nextHero (.walk 253)) (HazardPattern.afterPattern 10000 p (.walk 253)) ≤ 2 at afterRange
  rw [gammaAfter1005] at afterRange
  have possibilities : (d47417 p = 1 ∧ d47464 p = 0) ∨ (d47417 p = 2 ∧ d47464 p = 0) ∨ (d47417 p = 2 ∧ d47464 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39782 p pair.1
    have afterEq := eqIntro39806 p pair.2
    have combined := andIntro107744 p beforeEq guard
    have complete := andIntro107752 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39814 p pair.1
    have afterEq := eqIntro39806 p pair.2
    have combined := andIntro107760 p beforeEq guard
    have complete := andIntro107768 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro39814 p pair.1
    have afterEq := eqIntro39822 p pair.2
    have combined := andIntro107760 p beforeEq guard
    have complete := andIntro107776 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local1005 (p : Pattern) (guard : d379583 p = 1)
    (decreasing : bonus 253 (HazardPattern.afterPattern 10000 p (.walk 253)) < bonus 252 p) :
    NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 252 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 253) + NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 253))) + bonus 253 (HazardPattern.afterPattern 10000 p (.walk 253)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 253) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 253)) (HazardPattern.afterPattern 10000 p (.walk 253)) < bonus 252 p at decreasing
  rw [gammaAfter1005, at252] at decreasing
  have numeric := numeric1005 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 253)) (HazardPattern.afterPattern 10000 p (.walk 253))
  rw [oldBefore252, at252, literal, oldAfter1005, gammaAfter1005]
  exact numeric
theorem numeric1006 (p : Pattern) (guard : d379733 p = 1) (decreasing : d379779 p < d47417 p) :
    d50823 p + d47417 p ≤ (1 : Int) + d50823 p + d379779 p := by
  have beforeRange := bonus_range 252 p
  rw [at252] at beforeRange
  have afterRange := bonus_range 253 (HazardPattern.afterPattern 10000 p (.push 253 (.fill 254)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 253 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 253 (.fill 254))) ∧ bonus (HazardPattern.nextHero (.push 253 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 253 (.fill 254))) ≤ 2 at afterRange
  rw [gammaAfter1006] at afterRange
  have possibilities : (d47417 p = 1 ∧ d379779 p = 0) ∨ (d47417 p = 2 ∧ d379779 p = 0) ∨ (d47417 p = 2 ∧ d379779 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39782 p pair.1
    have afterEq := eqIntro39830 p pair.2
    have combined := andIntro107782 p beforeEq guard
    have complete := andIntro107783 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39814 p pair.1
    have afterEq := eqIntro39830 p pair.2
    have combined := andIntro107789 p beforeEq guard
    have complete := andIntro107783 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39814 p pair.1
    have afterEq := eqIntro39838 p pair.2
    have combined := andIntro107789 p beforeEq guard
    have complete := andIntro107790 p combined afterEq
    have bound := compare49829 p complete
    omega
theorem local1006 (p : Pattern) (guard : d379733 p = 1)
    (decreasing : bonus 253 (HazardPattern.afterPattern 10000 p (.push 253 (.fill 254))) < bonus 252 p) :
    NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 252 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 253 (.fill 254)) + NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 253 (.fill 254)))) + bonus 253 (HazardPattern.afterPattern 10000 p (.push 253 (.fill 254))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 253 (.fill 254)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 253 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 253 (.fill 254))) < bonus 252 p at decreasing
  rw [gammaAfter1006, at252] at decreasing
  have numeric := numeric1006 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 253 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 253 (.fill 254)))
  rw [oldBefore252, at252, literal, oldAfter1006, gammaAfter1006]
  exact numeric
theorem numeric1007 (p : Pattern) (guard : d379875 p = 1) (decreasing : d0 p < d47417 p) :
    d50823 p + d47417 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 252 p
  rw [at252] at beforeRange
  have afterRange := bonus_range 253 (HazardPattern.afterPattern 10000 p (.push 253 (.stay 254)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 253 (.stay 254))) (HazardPattern.afterPattern 10000 p (.push 253 (.stay 254))) ∧ bonus (HazardPattern.nextHero (.push 253 (.stay 254))) (HazardPattern.afterPattern 10000 p (.push 253 (.stay 254))) ≤ 2 at afterRange
  rw [gammaAfter1007] at afterRange
  have possibilities : (d47417 p = 1 ∧ d0 p = 0) ∨ (d47417 p = 2 ∧ d0 p = 0) ∨ (d47417 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39782 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107796 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39814 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107802 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39814 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro107802 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1007 (p : Pattern) (guard : d379875 p = 1)
    (decreasing : bonus 253 (HazardPattern.afterPattern 10000 p (.push 253 (.stay 254))) < bonus 252 p) :
    NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 252 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 253 (.stay 254)) + NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 253 (.stay 254)))) + bonus 253 (HazardPattern.afterPattern 10000 p (.push 253 (.stay 254))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 253 (.stay 254)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 253 (.stay 254))) (HazardPattern.afterPattern 10000 p (.push 253 (.stay 254))) < bonus 252 p at decreasing
  rw [gammaAfter1007, at252] at decreasing
  have numeric := numeric1007 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 253 (.stay 254))) (HazardPattern.afterPattern 10000 p (.push 253 (.stay 254)))
  rw [oldBefore252, at252, literal, oldAfter1007, gammaAfter1007]
  exact numeric
theorem numeric1008 (p : Pattern) (guard : d379277 p = 1) (decreasing : d47371 p < d47417 p) :
    d50823 p + d47417 p ≤ (0 : Int) + d50823 p + d47371 p := by
  have beforeRange := bonus_range 252 p
  rw [at252] at beforeRange
  have afterRange := bonus_range 251 (HazardPattern.afterPattern 10000 p (.walk 251))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 251)) (HazardPattern.afterPattern 10000 p (.walk 251)) ∧ bonus (HazardPattern.nextHero (.walk 251)) (HazardPattern.afterPattern 10000 p (.walk 251)) ≤ 2 at afterRange
  rw [gammaAfter1008] at afterRange
  have possibilities : (d47417 p = 1 ∧ d47371 p = 0) ∨ (d47417 p = 2 ∧ d47371 p = 0) ∨ (d47417 p = 2 ∧ d47371 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39782 p pair.1
    have afterEq := eqIntro39726 p pair.2
    have combined := andIntro107803 p guard beforeEq
    have complete := andIntro107811 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39814 p pair.1
    have afterEq := eqIntro39726 p pair.2
    have combined := andIntro107812 p guard beforeEq
    have complete := andIntro107820 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro39814 p pair.1
    have afterEq := eqIntro39742 p pair.2
    have combined := andIntro107812 p guard beforeEq
    have complete := andIntro107828 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local1008 (p : Pattern) (guard : d379277 p = 1)
    (decreasing : bonus 251 (HazardPattern.afterPattern 10000 p (.walk 251)) < bonus 252 p) :
    NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 252 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 251) + NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 251))) + bonus 251 (HazardPattern.afterPattern 10000 p (.walk 251)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 251) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 251)) (HazardPattern.afterPattern 10000 p (.walk 251)) < bonus 252 p at decreasing
  rw [gammaAfter1008, at252] at decreasing
  have numeric := numeric1008 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 251)) (HazardPattern.afterPattern 10000 p (.walk 251))
  rw [oldBefore252, at252, literal, oldAfter1008, gammaAfter1008]
  exact numeric
theorem numeric1009 (p : Pattern) (guard : d379882 p = 1) (decreasing : d379924 p < d47417 p) :
    d50823 p + d47417 p ≤ (1 : Int) + d50823 p + d379924 p := by
  have beforeRange := bonus_range 252 p
  rw [at252] at beforeRange
  have afterRange := bonus_range 251 (HazardPattern.afterPattern 10000 p (.push 251 (.fill 250)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 251 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 251 (.fill 250))) ∧ bonus (HazardPattern.nextHero (.push 251 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 251 (.fill 250))) ≤ 2 at afterRange
  rw [gammaAfter1009] at afterRange
  have possibilities : (d47417 p = 1 ∧ d379924 p = 0) ∨ (d47417 p = 2 ∧ d379924 p = 0) ∨ (d47417 p = 2 ∧ d379924 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39782 p pair.1
    have afterEq := eqIntro39846 p pair.2
    have combined := andIntro107834 p beforeEq guard
    have complete := andIntro107835 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39814 p pair.1
    have afterEq := eqIntro39846 p pair.2
    have combined := andIntro107841 p beforeEq guard
    have complete := andIntro107835 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39814 p pair.1
    have afterEq := eqIntro39854 p pair.2
    have combined := andIntro107841 p beforeEq guard
    have complete := andIntro107842 p combined afterEq
    have bound := compare49829 p complete
    omega
theorem local1009 (p : Pattern) (guard : d379882 p = 1)
    (decreasing : bonus 251 (HazardPattern.afterPattern 10000 p (.push 251 (.fill 250))) < bonus 252 p) :
    NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 252 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 251 (.fill 250)) + NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 251 (.fill 250)))) + bonus 251 (HazardPattern.afterPattern 10000 p (.push 251 (.fill 250))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 251 (.fill 250)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 251 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 251 (.fill 250))) < bonus 252 p at decreasing
  rw [gammaAfter1009, at252] at decreasing
  have numeric := numeric1009 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 251 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 251 (.fill 250)))
  rw [oldBefore252, at252, literal, oldAfter1009, gammaAfter1009]
  exact numeric
theorem numeric1010 (p : Pattern) (guard : d379271 p = 1) (decreasing : d0 p < d47417 p) :
    d50823 p + d47417 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 252 p
  rw [at252] at beforeRange
  have afterRange := bonus_range 251 (HazardPattern.afterPattern 10000 p (.push 251 (.stay 250)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 251 (.stay 250))) (HazardPattern.afterPattern 10000 p (.push 251 (.stay 250))) ∧ bonus (HazardPattern.nextHero (.push 251 (.stay 250))) (HazardPattern.afterPattern 10000 p (.push 251 (.stay 250))) ≤ 2 at afterRange
  rw [gammaAfter1010] at afterRange
  have possibilities : (d47417 p = 1 ∧ d0 p = 0) ∨ (d47417 p = 2 ∧ d0 p = 0) ∨ (d47417 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39782 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107848 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39814 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107854 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39814 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro107854 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1010 (p : Pattern) (guard : d379271 p = 1)
    (decreasing : bonus 251 (HazardPattern.afterPattern 10000 p (.push 251 (.stay 250))) < bonus 252 p) :
    NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 252 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 251 (.stay 250)) + NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 251 (.stay 250)))) + bonus 251 (HazardPattern.afterPattern 10000 p (.push 251 (.stay 250))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 251 (.stay 250)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 251 (.stay 250))) (HazardPattern.afterPattern 10000 p (.push 251 (.stay 250))) < bonus 252 p at decreasing
  rw [gammaAfter1010, at252] at decreasing
  have numeric := numeric1010 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 251 (.stay 250))) (HazardPattern.afterPattern 10000 p (.push 251 (.stay 250)))
  rw [oldBefore252, at252, literal, oldAfter1010, gammaAfter1010]
  exact numeric
theorem numeric1011 (p : Pattern) (guard : d380014 p = 1) (decreasing : d47512 p < d47464 p) :
    d50823 p + d47464 p ≤ (0 : Int) + d50823 p + d47512 p := by
  have beforeRange := bonus_range 253 p
  rw [at253] at beforeRange
  have afterRange := bonus_range 254 (HazardPattern.afterPattern 10000 p (.walk 254))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 254)) (HazardPattern.afterPattern 10000 p (.walk 254)) ∧ bonus (HazardPattern.nextHero (.walk 254)) (HazardPattern.afterPattern 10000 p (.walk 254)) ≤ 2 at afterRange
  rw [gammaAfter1011] at afterRange
  have possibilities : (d47464 p = 1 ∧ d47512 p = 0) ∨ (d47464 p = 2 ∧ d47512 p = 0) ∨ (d47464 p = 2 ∧ d47512 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39822 p pair.1
    have afterEq := eqIntro39862 p pair.2
    have combined := andIntro107862 p beforeEq guard
    have complete := andIntro107870 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39870 p pair.1
    have afterEq := eqIntro39862 p pair.2
    have combined := andIntro107878 p beforeEq guard
    have complete := andIntro107886 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro39870 p pair.1
    have afterEq := eqIntro39878 p pair.2
    have combined := andIntro107878 p beforeEq guard
    have complete := andIntro107894 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local1011 (p : Pattern) (guard : d380014 p = 1)
    (decreasing : bonus 254 (HazardPattern.afterPattern 10000 p (.walk 254)) < bonus 253 p) :
    NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 253 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 254) + NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 254))) + bonus 254 (HazardPattern.afterPattern 10000 p (.walk 254)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 254) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 254)) (HazardPattern.afterPattern 10000 p (.walk 254)) < bonus 253 p at decreasing
  rw [gammaAfter1011, at253] at decreasing
  have numeric := numeric1011 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 254)) (HazardPattern.afterPattern 10000 p (.walk 254))
  rw [oldBefore253, at253, literal, oldAfter1011, gammaAfter1011]
  exact numeric
theorem numeric1012 (p : Pattern) (guard : d380167 p = 1) (decreasing : d380214 p < d47464 p) :
    d50823 p + d47464 p ≤ (1 : Int) + d50823 p + d380214 p := by
  have beforeRange := bonus_range 253 p
  rw [at253] at beforeRange
  have afterRange := bonus_range 254 (HazardPattern.afterPattern 10000 p (.push 254 (.fill 255)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 254 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 254 (.fill 255))) ∧ bonus (HazardPattern.nextHero (.push 254 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 254 (.fill 255))) ≤ 2 at afterRange
  rw [gammaAfter1012] at afterRange
  have possibilities : (d47464 p = 1 ∧ d380214 p = 0) ∨ (d47464 p = 2 ∧ d380214 p = 0) ∨ (d47464 p = 2 ∧ d380214 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39822 p pair.1
    have afterEq := eqIntro39887 p pair.2
    have combined := andIntro107901 p beforeEq guard
    have complete := andIntro107902 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39870 p pair.1
    have afterEq := eqIntro39887 p pair.2
    have combined := andIntro107909 p beforeEq guard
    have complete := andIntro107902 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39870 p pair.1
    have afterEq := eqIntro39896 p pair.2
    have combined := andIntro107909 p beforeEq guard
    have complete := andIntro107910 p combined afterEq
    have bound := compare49829 p complete
    omega
theorem local1012 (p : Pattern) (guard : d380167 p = 1)
    (decreasing : bonus 254 (HazardPattern.afterPattern 10000 p (.push 254 (.fill 255))) < bonus 253 p) :
    NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 253 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 254 (.fill 255)) + NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 254 (.fill 255)))) + bonus 254 (HazardPattern.afterPattern 10000 p (.push 254 (.fill 255))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 254 (.fill 255)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 254 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 254 (.fill 255))) < bonus 253 p at decreasing
  rw [gammaAfter1012, at253] at decreasing
  have numeric := numeric1012 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 254 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 254 (.fill 255)))
  rw [oldBefore253, at253, literal, oldAfter1012, gammaAfter1012]
  exact numeric
theorem numeric1013 (p : Pattern) (guard : d380312 p = 1) (decreasing : d0 p < d47464 p) :
    d50823 p + d47464 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 253 p
  rw [at253] at beforeRange
  have afterRange := bonus_range 254 (HazardPattern.afterPattern 10000 p (.push 254 (.stay 255)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 254 (.stay 255))) (HazardPattern.afterPattern 10000 p (.push 254 (.stay 255))) ∧ bonus (HazardPattern.nextHero (.push 254 (.stay 255))) (HazardPattern.afterPattern 10000 p (.push 254 (.stay 255))) ≤ 2 at afterRange
  rw [gammaAfter1013] at afterRange
  have possibilities : (d47464 p = 1 ∧ d0 p = 0) ∨ (d47464 p = 2 ∧ d0 p = 0) ∨ (d47464 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39822 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107917 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39870 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107924 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39870 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro107924 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1013 (p : Pattern) (guard : d380312 p = 1)
    (decreasing : bonus 254 (HazardPattern.afterPattern 10000 p (.push 254 (.stay 255))) < bonus 253 p) :
    NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 253 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 254 (.stay 255)) + NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 254 (.stay 255)))) + bonus 254 (HazardPattern.afterPattern 10000 p (.push 254 (.stay 255))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 254 (.stay 255)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 254 (.stay 255))) (HazardPattern.afterPattern 10000 p (.push 254 (.stay 255))) < bonus 253 p at decreasing
  rw [gammaAfter1013, at253] at decreasing
  have numeric := numeric1013 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 254 (.stay 255))) (HazardPattern.afterPattern 10000 p (.push 254 (.stay 255)))
  rw [oldBefore253, at253, literal, oldAfter1013, gammaAfter1013]
  exact numeric
theorem numeric1014 (p : Pattern) (guard : d379583 p = 1) (decreasing : d47417 p < d47464 p) :
    d50823 p + d47464 p ≤ (0 : Int) + d50823 p + d47417 p := by
  have beforeRange := bonus_range 253 p
  rw [at253] at beforeRange
  have afterRange := bonus_range 252 (HazardPattern.afterPattern 10000 p (.walk 252))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 252)) (HazardPattern.afterPattern 10000 p (.walk 252)) ∧ bonus (HazardPattern.nextHero (.walk 252)) (HazardPattern.afterPattern 10000 p (.walk 252)) ≤ 2 at afterRange
  rw [gammaAfter1014] at afterRange
  have possibilities : (d47464 p = 1 ∧ d47417 p = 0) ∨ (d47464 p = 2 ∧ d47417 p = 0) ∨ (d47464 p = 2 ∧ d47417 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39822 p pair.1
    have afterEq := eqIntro39766 p pair.2
    have combined := andIntro107925 p guard beforeEq
    have complete := andIntro107933 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39870 p pair.1
    have afterEq := eqIntro39766 p pair.2
    have combined := andIntro107934 p guard beforeEq
    have complete := andIntro107942 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro39870 p pair.1
    have afterEq := eqIntro39782 p pair.2
    have combined := andIntro107934 p guard beforeEq
    have complete := andIntro107950 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local1014 (p : Pattern) (guard : d379583 p = 1)
    (decreasing : bonus 252 (HazardPattern.afterPattern 10000 p (.walk 252)) < bonus 253 p) :
    NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 253 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 252) + NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 252))) + bonus 252 (HazardPattern.afterPattern 10000 p (.walk 252)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 252) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 252)) (HazardPattern.afterPattern 10000 p (.walk 252)) < bonus 253 p at decreasing
  rw [gammaAfter1014, at253] at decreasing
  have numeric := numeric1014 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 252)) (HazardPattern.afterPattern 10000 p (.walk 252))
  rw [oldBefore253, at253, literal, oldAfter1014, gammaAfter1014]
  exact numeric
theorem numeric1015 (p : Pattern) (guard : d380319 p = 1) (decreasing : d380362 p < d47464 p) :
    d50823 p + d47464 p ≤ (1 : Int) + d50823 p + d380362 p := by
  have beforeRange := bonus_range 253 p
  rw [at253] at beforeRange
  have afterRange := bonus_range 252 (HazardPattern.afterPattern 10000 p (.push 252 (.fill 251)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 252 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 252 (.fill 251))) ∧ bonus (HazardPattern.nextHero (.push 252 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 252 (.fill 251))) ≤ 2 at afterRange
  rw [gammaAfter1015] at afterRange
  have possibilities : (d47464 p = 1 ∧ d380362 p = 0) ∨ (d47464 p = 2 ∧ d380362 p = 0) ∨ (d47464 p = 2 ∧ d380362 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39822 p pair.1
    have afterEq := eqIntro39904 p pair.2
    have combined := andIntro107956 p beforeEq guard
    have complete := andIntro107957 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39870 p pair.1
    have afterEq := eqIntro39904 p pair.2
    have combined := andIntro107963 p beforeEq guard
    have complete := andIntro107957 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39870 p pair.1
    have afterEq := eqIntro39912 p pair.2
    have combined := andIntro107963 p beforeEq guard
    have complete := andIntro107964 p combined afterEq
    have bound := compare49829 p complete
    omega
theorem local1015 (p : Pattern) (guard : d380319 p = 1)
    (decreasing : bonus 252 (HazardPattern.afterPattern 10000 p (.push 252 (.fill 251))) < bonus 253 p) :
    NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 253 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 252 (.fill 251)) + NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 252 (.fill 251)))) + bonus 252 (HazardPattern.afterPattern 10000 p (.push 252 (.fill 251))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 252 (.fill 251)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 252 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 252 (.fill 251))) < bonus 253 p at decreasing
  rw [gammaAfter1015, at253] at decreasing
  have numeric := numeric1015 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 252 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 252 (.fill 251)))
  rw [oldBefore253, at253, literal, oldAfter1015, gammaAfter1015]
  exact numeric
theorem numeric1016 (p : Pattern) (guard : d379563 p = 1) (decreasing : d0 p < d47464 p) :
    d50823 p + d47464 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 253 p
  rw [at253] at beforeRange
  have afterRange := bonus_range 252 (HazardPattern.afterPattern 10000 p (.push 252 (.stay 251)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 252 (.stay 251))) (HazardPattern.afterPattern 10000 p (.push 252 (.stay 251))) ∧ bonus (HazardPattern.nextHero (.push 252 (.stay 251))) (HazardPattern.afterPattern 10000 p (.push 252 (.stay 251))) ≤ 2 at afterRange
  rw [gammaAfter1016] at afterRange
  have possibilities : (d47464 p = 1 ∧ d0 p = 0) ∨ (d47464 p = 2 ∧ d0 p = 0) ∨ (d47464 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39822 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107970 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39870 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro107976 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39870 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro107976 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1016 (p : Pattern) (guard : d379563 p = 1)
    (decreasing : bonus 252 (HazardPattern.afterPattern 10000 p (.push 252 (.stay 251))) < bonus 253 p) :
    NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 253 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 252 (.stay 251)) + NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 252 (.stay 251)))) + bonus 252 (HazardPattern.afterPattern 10000 p (.push 252 (.stay 251))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 252 (.stay 251)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 252 (.stay 251))) (HazardPattern.afterPattern 10000 p (.push 252 (.stay 251))) < bonus 253 p at decreasing
  rw [gammaAfter1016, at253] at decreasing
  have numeric := numeric1016 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 252 (.stay 251))) (HazardPattern.afterPattern 10000 p (.push 252 (.stay 251)))
  rw [oldBefore253, at253, literal, oldAfter1016, gammaAfter1016]
  exact numeric
theorem numeric1017 (p : Pattern) (guard : d380454 p = 1) (decreasing : d47561 p < d47512 p) :
    d50823 p + d47512 p ≤ (0 : Int) + d50823 p + d47561 p := by
  have beforeRange := bonus_range 254 p
  rw [at254] at beforeRange
  have afterRange := bonus_range 255 (HazardPattern.afterPattern 10000 p (.walk 255))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 255)) (HazardPattern.afterPattern 10000 p (.walk 255)) ∧ bonus (HazardPattern.nextHero (.walk 255)) (HazardPattern.afterPattern 10000 p (.walk 255)) ≤ 2 at afterRange
  rw [gammaAfter1017] at afterRange
  have possibilities : (d47512 p = 1 ∧ d47561 p = 0) ∨ (d47512 p = 2 ∧ d47561 p = 0) ∨ (d47512 p = 2 ∧ d47561 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39878 p pair.1
    have afterEq := eqIntro39921 p pair.2
    have combined := andIntro107985 p beforeEq guard
    have complete := andIntro107994 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39929 p pair.1
    have afterEq := eqIntro39921 p pair.2
    have combined := andIntro108003 p beforeEq guard
    have complete := andIntro108012 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro39929 p pair.1
    have afterEq := eqIntro39938 p pair.2
    have combined := andIntro108003 p beforeEq guard
    have complete := andIntro108021 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local1017 (p : Pattern) (guard : d380454 p = 1)
    (decreasing : bonus 255 (HazardPattern.afterPattern 10000 p (.walk 255)) < bonus 254 p) :
    NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 254 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 255) + NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 255))) + bonus 255 (HazardPattern.afterPattern 10000 p (.walk 255)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 255) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 255)) (HazardPattern.afterPattern 10000 p (.walk 255)) < bonus 254 p at decreasing
  rw [gammaAfter1017, at254] at decreasing
  have numeric := numeric1017 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 255)) (HazardPattern.afterPattern 10000 p (.walk 255))
  rw [oldBefore254, at254, literal, oldAfter1017, gammaAfter1017]
  exact numeric
theorem numeric1018 (p : Pattern) (guard : d380610 p = 1) (decreasing : d380658 p < d47512 p) :
    d50823 p + d47512 p ≤ (1 : Int) + d50823 p + d380658 p := by
  have beforeRange := bonus_range 254 p
  rw [at254] at beforeRange
  have afterRange := bonus_range 255 (HazardPattern.afterPattern 10000 p (.push 255 (.fill 256)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 255 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 255 (.fill 256))) ∧ bonus (HazardPattern.nextHero (.push 255 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 255 (.fill 256))) ≤ 2 at afterRange
  rw [gammaAfter1018] at afterRange
  have possibilities : (d47512 p = 1 ∧ d380658 p = 0) ∨ (d47512 p = 2 ∧ d380658 p = 0) ∨ (d47512 p = 2 ∧ d380658 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39878 p pair.1
    have afterEq := eqIntro39947 p pair.2
    have combined := andIntro108028 p beforeEq guard
    have complete := andIntro108029 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39929 p pair.1
    have afterEq := eqIntro39947 p pair.2
    have combined := andIntro108036 p beforeEq guard
    have complete := andIntro108029 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39929 p pair.1
    have afterEq := eqIntro39948 p pair.2
    have combined := andIntro108036 p beforeEq guard
    have complete := andIntro108037 p combined afterEq
    have bound := compare49829 p complete
    omega
theorem local1018 (p : Pattern) (guard : d380610 p = 1)
    (decreasing : bonus 255 (HazardPattern.afterPattern 10000 p (.push 255 (.fill 256))) < bonus 254 p) :
    NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 254 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 255 (.fill 256)) + NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 255 (.fill 256)))) + bonus 255 (HazardPattern.afterPattern 10000 p (.push 255 (.fill 256))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 255 (.fill 256)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 255 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 255 (.fill 256))) < bonus 254 p at decreasing
  rw [gammaAfter1018, at254] at decreasing
  have numeric := numeric1018 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 255 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 255 (.fill 256)))
  rw [oldBefore254, at254, literal, oldAfter1018, gammaAfter1018]
  exact numeric
theorem numeric1019 (p : Pattern) (guard : d380710 p = 1) (decreasing : d0 p < d47512 p) :
    d50823 p + d47512 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 254 p
  rw [at254] at beforeRange
  have afterRange := bonus_range 255 (HazardPattern.afterPattern 10000 p (.push 255 (.stay 256)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 255 (.stay 256))) (HazardPattern.afterPattern 10000 p (.push 255 (.stay 256))) ∧ bonus (HazardPattern.nextHero (.push 255 (.stay 256))) (HazardPattern.afterPattern 10000 p (.push 255 (.stay 256))) ≤ 2 at afterRange
  rw [gammaAfter1019] at afterRange
  have possibilities : (d47512 p = 1 ∧ d0 p = 0) ∨ (d47512 p = 2 ∧ d0 p = 0) ∨ (d47512 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39878 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108044 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39929 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108051 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39929 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108051 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1019 (p : Pattern) (guard : d380710 p = 1)
    (decreasing : bonus 255 (HazardPattern.afterPattern 10000 p (.push 255 (.stay 256))) < bonus 254 p) :
    NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 254 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 255 (.stay 256)) + NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 255 (.stay 256)))) + bonus 255 (HazardPattern.afterPattern 10000 p (.push 255 (.stay 256))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 255 (.stay 256)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 255 (.stay 256))) (HazardPattern.afterPattern 10000 p (.push 255 (.stay 256))) < bonus 254 p at decreasing
  rw [gammaAfter1019, at254] at decreasing
  have numeric := numeric1019 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 255 (.stay 256))) (HazardPattern.afterPattern 10000 p (.push 255 (.stay 256)))
  rw [oldBefore254, at254, literal, oldAfter1019, gammaAfter1019]
  exact numeric
theorem numeric1020 (p : Pattern) (guard : d380014 p = 1) (decreasing : d47464 p < d47512 p) :
    d50823 p + d47512 p ≤ (0 : Int) + d50823 p + d47464 p := by
  have beforeRange := bonus_range 254 p
  rw [at254] at beforeRange
  have afterRange := bonus_range 253 (HazardPattern.afterPattern 10000 p (.walk 253))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 253)) (HazardPattern.afterPattern 10000 p (.walk 253)) ∧ bonus (HazardPattern.nextHero (.walk 253)) (HazardPattern.afterPattern 10000 p (.walk 253)) ≤ 2 at afterRange
  rw [gammaAfter1020] at afterRange
  have possibilities : (d47512 p = 1 ∧ d47464 p = 0) ∨ (d47512 p = 2 ∧ d47464 p = 0) ∨ (d47512 p = 2 ∧ d47464 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39878 p pair.1
    have afterEq := eqIntro39806 p pair.2
    have combined := andIntro108052 p guard beforeEq
    have complete := andIntro108060 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39929 p pair.1
    have afterEq := eqIntro39806 p pair.2
    have combined := andIntro108061 p guard beforeEq
    have complete := andIntro108069 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro39929 p pair.1
    have afterEq := eqIntro39822 p pair.2
    have combined := andIntro108061 p guard beforeEq
    have complete := andIntro108077 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local1020 (p : Pattern) (guard : d380014 p = 1)
    (decreasing : bonus 253 (HazardPattern.afterPattern 10000 p (.walk 253)) < bonus 254 p) :
    NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 254 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 253) + NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 253))) + bonus 253 (HazardPattern.afterPattern 10000 p (.walk 253)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 253) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 253)) (HazardPattern.afterPattern 10000 p (.walk 253)) < bonus 254 p at decreasing
  rw [gammaAfter1020, at254] at decreasing
  have numeric := numeric1020 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 253)) (HazardPattern.afterPattern 10000 p (.walk 253))
  rw [oldBefore254, at254, literal, oldAfter1020, gammaAfter1020]
  exact numeric
theorem numeric1021 (p : Pattern) (guard : d380717 p = 1) (decreasing : d380761 p < d47512 p) :
    d50823 p + d47512 p ≤ (1 : Int) + d50823 p + d380761 p := by
  have beforeRange := bonus_range 254 p
  rw [at254] at beforeRange
  have afterRange := bonus_range 253 (HazardPattern.afterPattern 10000 p (.push 253 (.fill 252)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 253 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 253 (.fill 252))) ∧ bonus (HazardPattern.nextHero (.push 253 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 253 (.fill 252))) ≤ 2 at afterRange
  rw [gammaAfter1021] at afterRange
  have possibilities : (d47512 p = 1 ∧ d380761 p = 0) ∨ (d47512 p = 2 ∧ d380761 p = 0) ∨ (d47512 p = 2 ∧ d380761 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39878 p pair.1
    have afterEq := eqIntro39956 p pair.2
    have combined := andIntro108083 p beforeEq guard
    have complete := andIntro108084 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39929 p pair.1
    have afterEq := eqIntro39956 p pair.2
    have combined := andIntro108090 p beforeEq guard
    have complete := andIntro108084 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39929 p pair.1
    have afterEq := eqIntro39964 p pair.2
    have combined := andIntro108090 p beforeEq guard
    have complete := andIntro108091 p combined afterEq
    have bound := compare49829 p complete
    omega
theorem local1021 (p : Pattern) (guard : d380717 p = 1)
    (decreasing : bonus 253 (HazardPattern.afterPattern 10000 p (.push 253 (.fill 252))) < bonus 254 p) :
    NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 254 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 253 (.fill 252)) + NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 253 (.fill 252)))) + bonus 253 (HazardPattern.afterPattern 10000 p (.push 253 (.fill 252))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 253 (.fill 252)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 253 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 253 (.fill 252))) < bonus 254 p at decreasing
  rw [gammaAfter1021, at254] at decreasing
  have numeric := numeric1021 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 253 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 253 (.fill 252)))
  rw [oldBefore254, at254, literal, oldAfter1021, gammaAfter1021]
  exact numeric
theorem numeric1022 (p : Pattern) (guard : d379875 p = 1) (decreasing : d0 p < d47512 p) :
    d50823 p + d47512 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 254 p
  rw [at254] at beforeRange
  have afterRange := bonus_range 253 (HazardPattern.afterPattern 10000 p (.push 253 (.stay 252)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 253 (.stay 252))) (HazardPattern.afterPattern 10000 p (.push 253 (.stay 252))) ∧ bonus (HazardPattern.nextHero (.push 253 (.stay 252))) (HazardPattern.afterPattern 10000 p (.push 253 (.stay 252))) ≤ 2 at afterRange
  rw [gammaAfter1022] at afterRange
  have possibilities : (d47512 p = 1 ∧ d0 p = 0) ∨ (d47512 p = 2 ∧ d0 p = 0) ∨ (d47512 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39878 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108097 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39929 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108103 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39929 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108103 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1022 (p : Pattern) (guard : d379875 p = 1)
    (decreasing : bonus 253 (HazardPattern.afterPattern 10000 p (.push 253 (.stay 252))) < bonus 254 p) :
    NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 254 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 253 (.stay 252)) + NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 253 (.stay 252)))) + bonus 253 (HazardPattern.afterPattern 10000 p (.push 253 (.stay 252))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 253 (.stay 252)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 253 (.stay 252))) (HazardPattern.afterPattern 10000 p (.push 253 (.stay 252))) < bonus 254 p at decreasing
  rw [gammaAfter1022, at254] at decreasing
  have numeric := numeric1022 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 253 (.stay 252))) (HazardPattern.afterPattern 10000 p (.push 253 (.stay 252)))
  rw [oldBefore254, at254, literal, oldAfter1022, gammaAfter1022]
  exact numeric
theorem numeric1023 (p : Pattern) (guard : d380855 p = 1) (decreasing : d47611 p < d47561 p) :
    d50823 p + d47561 p ≤ (0 : Int) + d50823 p + d47611 p := by
  have beforeRange := bonus_range 255 p
  rw [at255] at beforeRange
  have afterRange := bonus_range 256 (HazardPattern.afterPattern 10000 p (.walk 256))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 256)) (HazardPattern.afterPattern 10000 p (.walk 256)) ∧ bonus (HazardPattern.nextHero (.walk 256)) (HazardPattern.afterPattern 10000 p (.walk 256)) ≤ 2 at afterRange
  rw [gammaAfter1023] at afterRange
  have possibilities : (d47561 p = 1 ∧ d47611 p = 0) ∨ (d47561 p = 2 ∧ d47611 p = 0) ∨ (d47561 p = 2 ∧ d47611 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39938 p pair.1
    have afterEq := eqIntro39973 p pair.2
    have combined := andIntro108112 p beforeEq guard
    have complete := andIntro108121 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39982 p pair.1
    have afterEq := eqIntro39973 p pair.2
    have combined := andIntro108130 p beforeEq guard
    have complete := andIntro108131 p combined afterEq
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro39982 p pair.1
    have afterEq := eqIntro39983 p pair.2
    have combined := andIntro108130 p beforeEq guard
    have complete := andIntro108132 p combined afterEq
    have bound := compare41207 p complete
    omega
theorem local1023 (p : Pattern) (guard : d380855 p = 1)
    (decreasing : bonus 256 (HazardPattern.afterPattern 10000 p (.walk 256)) < bonus 255 p) :
    NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 255 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 256) + NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 256))) + bonus 256 (HazardPattern.afterPattern 10000 p (.walk 256)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 256) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 256)) (HazardPattern.afterPattern 10000 p (.walk 256)) < bonus 255 p at decreasing
  rw [gammaAfter1023, at255] at decreasing
  have numeric := numeric1023 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 256)) (HazardPattern.afterPattern 10000 p (.walk 256))
  rw [oldBefore255, at255, literal, oldAfter1023, gammaAfter1023]
  exact numeric
theorem numeric1024 (p : Pattern) (guard : d380914 p = 1) (decreasing : d0 p < d47561 p) :
    d50823 p + d47561 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 255 p
  rw [at255] at beforeRange
  have afterRange := bonus_range 256 (HazardPattern.afterPattern 10000 p (.push 256 (.fill 257)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 256 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 256 (.fill 257))) ∧ bonus (HazardPattern.nextHero (.push 256 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 256 (.fill 257))) ≤ 2 at afterRange
  rw [gammaAfter1024] at afterRange
  have possibilities : (d47561 p = 1 ∧ d0 p = 0) ∨ (d47561 p = 2 ∧ d0 p = 0) ∨ (d47561 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39938 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108139 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39982 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108146 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39982 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108146 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1024 (p : Pattern) (guard : d380914 p = 1)
    (decreasing : bonus 256 (HazardPattern.afterPattern 10000 p (.push 256 (.fill 257))) < bonus 255 p) :
    NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 255 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 256 (.fill 257)) + NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 256 (.fill 257)))) + bonus 256 (HazardPattern.afterPattern 10000 p (.push 256 (.fill 257))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 256 (.fill 257)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 256 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 256 (.fill 257))) < bonus 255 p at decreasing
  rw [gammaAfter1024, at255] at decreasing
  have numeric := numeric1024 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 256 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 256 (.fill 257)))
  rw [oldBefore255, at255, literal, oldAfter1024, gammaAfter1024]
  exact numeric
theorem numeric1025 (p : Pattern) (guard : d380918 p = 1) (decreasing : d0 p < d47561 p) :
    d50823 p + d47561 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 255 p
  rw [at255] at beforeRange
  have afterRange := bonus_range 256 (HazardPattern.afterPattern 10000 p (.push 256 (.stay 257)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 256 (.stay 257))) (HazardPattern.afterPattern 10000 p (.push 256 (.stay 257))) ∧ bonus (HazardPattern.nextHero (.push 256 (.stay 257))) (HazardPattern.afterPattern 10000 p (.push 256 (.stay 257))) ≤ 2 at afterRange
  rw [gammaAfter1025] at afterRange
  have possibilities : (d47561 p = 1 ∧ d0 p = 0) ∨ (d47561 p = 2 ∧ d0 p = 0) ∨ (d47561 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39938 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108153 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39982 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108160 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39982 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108160 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1025 (p : Pattern) (guard : d380918 p = 1)
    (decreasing : bonus 256 (HazardPattern.afterPattern 10000 p (.push 256 (.stay 257))) < bonus 255 p) :
    NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 255 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 256 (.stay 257)) + NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 256 (.stay 257)))) + bonus 256 (HazardPattern.afterPattern 10000 p (.push 256 (.stay 257))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 256 (.stay 257)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 256 (.stay 257))) (HazardPattern.afterPattern 10000 p (.push 256 (.stay 257))) < bonus 255 p at decreasing
  rw [gammaAfter1025, at255] at decreasing
  have numeric := numeric1025 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 256 (.stay 257))) (HazardPattern.afterPattern 10000 p (.push 256 (.stay 257)))
  rw [oldBefore255, at255, literal, oldAfter1025, gammaAfter1025]
  exact numeric
theorem numeric1026 (p : Pattern) (guard : d380454 p = 1) (decreasing : d47512 p < d47561 p) :
    d50823 p + d47561 p ≤ (0 : Int) + d50823 p + d47512 p := by
  have beforeRange := bonus_range 255 p
  rw [at255] at beforeRange
  have afterRange := bonus_range 254 (HazardPattern.afterPattern 10000 p (.walk 254))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 254)) (HazardPattern.afterPattern 10000 p (.walk 254)) ∧ bonus (HazardPattern.nextHero (.walk 254)) (HazardPattern.afterPattern 10000 p (.walk 254)) ≤ 2 at afterRange
  rw [gammaAfter1026] at afterRange
  have possibilities : (d47561 p = 1 ∧ d47512 p = 0) ∨ (d47561 p = 2 ∧ d47512 p = 0) ∨ (d47561 p = 2 ∧ d47512 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39938 p pair.1
    have afterEq := eqIntro39862 p pair.2
    have combined := andIntro108161 p guard beforeEq
    have complete := andIntro108170 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39982 p pair.1
    have afterEq := eqIntro39862 p pair.2
    have combined := andIntro108171 p guard beforeEq
    have complete := andIntro108180 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro39982 p pair.1
    have afterEq := eqIntro39878 p pair.2
    have combined := andIntro108171 p guard beforeEq
    have complete := andIntro108189 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local1026 (p : Pattern) (guard : d380454 p = 1)
    (decreasing : bonus 254 (HazardPattern.afterPattern 10000 p (.walk 254)) < bonus 255 p) :
    NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 255 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 254) + NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 254))) + bonus 254 (HazardPattern.afterPattern 10000 p (.walk 254)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 254) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 254)) (HazardPattern.afterPattern 10000 p (.walk 254)) < bonus 255 p at decreasing
  rw [gammaAfter1026, at255] at decreasing
  have numeric := numeric1026 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 254)) (HazardPattern.afterPattern 10000 p (.walk 254))
  rw [oldBefore255, at255, literal, oldAfter1026, gammaAfter1026]
  exact numeric
theorem numeric1027 (p : Pattern) (guard : d380925 p = 1) (decreasing : d380970 p < d47561 p) :
    d50823 p + d47561 p ≤ (1 : Int) + d50823 p + d380970 p := by
  have beforeRange := bonus_range 255 p
  rw [at255] at beforeRange
  have afterRange := bonus_range 254 (HazardPattern.afterPattern 10000 p (.push 254 (.fill 253)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 254 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 254 (.fill 253))) ∧ bonus (HazardPattern.nextHero (.push 254 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 254 (.fill 253))) ≤ 2 at afterRange
  rw [gammaAfter1027] at afterRange
  have possibilities : (d47561 p = 1 ∧ d380970 p = 0) ∨ (d47561 p = 2 ∧ d380970 p = 0) ∨ (d47561 p = 2 ∧ d380970 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39938 p pair.1
    have afterEq := eqIntro39991 p pair.2
    have combined := andIntro108196 p beforeEq guard
    have complete := andIntro108197 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39982 p pair.1
    have afterEq := eqIntro39991 p pair.2
    have combined := andIntro108204 p beforeEq guard
    have complete := andIntro108197 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39982 p pair.1
    have afterEq := eqIntro39999 p pair.2
    have combined := andIntro108204 p beforeEq guard
    have complete := andIntro108205 p combined afterEq
    have bound := compare49829 p complete
    omega
theorem local1027 (p : Pattern) (guard : d380925 p = 1)
    (decreasing : bonus 254 (HazardPattern.afterPattern 10000 p (.push 254 (.fill 253))) < bonus 255 p) :
    NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 255 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 254 (.fill 253)) + NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 254 (.fill 253)))) + bonus 254 (HazardPattern.afterPattern 10000 p (.push 254 (.fill 253))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 254 (.fill 253)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 254 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 254 (.fill 253))) < bonus 255 p at decreasing
  rw [gammaAfter1027, at255] at decreasing
  have numeric := numeric1027 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 254 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 254 (.fill 253)))
  rw [oldBefore255, at255, literal, oldAfter1027, gammaAfter1027]
  exact numeric
theorem numeric1028 (p : Pattern) (guard : d380312 p = 1) (decreasing : d0 p < d47561 p) :
    d50823 p + d47561 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 255 p
  rw [at255] at beforeRange
  have afterRange := bonus_range 254 (HazardPattern.afterPattern 10000 p (.push 254 (.stay 253)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 254 (.stay 253))) (HazardPattern.afterPattern 10000 p (.push 254 (.stay 253))) ∧ bonus (HazardPattern.nextHero (.push 254 (.stay 253))) (HazardPattern.afterPattern 10000 p (.push 254 (.stay 253))) ≤ 2 at afterRange
  rw [gammaAfter1028] at afterRange
  have possibilities : (d47561 p = 1 ∧ d0 p = 0) ∨ (d47561 p = 2 ∧ d0 p = 0) ∨ (d47561 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39938 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108212 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro39982 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108219 p guard beforeEq
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro39982 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108219 p guard beforeEq
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1028 (p : Pattern) (guard : d380312 p = 1)
    (decreasing : bonus 254 (HazardPattern.afterPattern 10000 p (.push 254 (.stay 253))) < bonus 255 p) :
    NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 255 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 254 (.stay 253)) + NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 254 (.stay 253)))) + bonus 254 (HazardPattern.afterPattern 10000 p (.push 254 (.stay 253))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 254 (.stay 253)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 254 (.stay 253))) (HazardPattern.afterPattern 10000 p (.push 254 (.stay 253))) < bonus 255 p at decreasing
  rw [gammaAfter1028, at255] at decreasing
  have numeric := numeric1028 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 254 (.stay 253))) (HazardPattern.afterPattern 10000 p (.push 254 (.stay 253)))
  rw [oldBefore255, at255, literal, oldAfter1028, gammaAfter1028]
  exact numeric
theorem numeric1029 (p : Pattern) (guard : d381066 p = 1) (decreasing : d0 p < d47611 p) :
    d50823 p + d47611 p ≤ (0 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 256 p
  rw [at256] at beforeRange
  have afterRange := bonus_range 257 (HazardPattern.afterPattern 10000 p (.walk 257))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 257)) (HazardPattern.afterPattern 10000 p (.walk 257)) ∧ bonus (HazardPattern.nextHero (.walk 257)) (HazardPattern.afterPattern 10000 p (.walk 257)) ≤ 2 at afterRange
  rw [gammaAfter1029] at afterRange
  have possibilities : (d47611 p = 1 ∧ d0 p = 0) ∨ (d47611 p = 2 ∧ d0 p = 0) ∨ (d47611 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39983 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108228 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro40008 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108229 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro40008 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108229 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare41207 p complete
    omega
theorem local1029 (p : Pattern) (guard : d381066 p = 1)
    (decreasing : bonus 257 (HazardPattern.afterPattern 10000 p (.walk 257)) < bonus 256 p) :
    NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 256 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 257) + NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 257))) + bonus 257 (HazardPattern.afterPattern 10000 p (.walk 257)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 257) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 257)) (HazardPattern.afterPattern 10000 p (.walk 257)) < bonus 256 p at decreasing
  rw [gammaAfter1029, at256] at decreasing
  have numeric := numeric1029 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 257)) (HazardPattern.afterPattern 10000 p (.walk 257))
  rw [oldBefore256, at256, literal, oldAfter1029, gammaAfter1029]
  exact numeric
theorem numeric1030 (p : Pattern) (guard : d381075 p = 1) (decreasing : d0 p < d47611 p) :
    d50823 p + d47611 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 256 p
  rw [at256] at beforeRange
  have afterRange := bonus_range 257 (HazardPattern.afterPattern 10000 p (.push 257 (.fill 258)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 257 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 257 (.fill 258))) ∧ bonus (HazardPattern.nextHero (.push 257 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 257 (.fill 258))) ≤ 2 at afterRange
  rw [gammaAfter1030] at afterRange
  have possibilities : (d47611 p = 1 ∧ d0 p = 0) ∨ (d47611 p = 2 ∧ d0 p = 0) ∨ (d47611 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39983 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108236 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro40008 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108237 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro40008 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108237 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1030 (p : Pattern) (guard : d381075 p = 1)
    (decreasing : bonus 257 (HazardPattern.afterPattern 10000 p (.push 257 (.fill 258))) < bonus 256 p) :
    NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 256 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 257 (.fill 258)) + NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 257 (.fill 258)))) + bonus 257 (HazardPattern.afterPattern 10000 p (.push 257 (.fill 258))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 257 (.fill 258)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 257 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 257 (.fill 258))) < bonus 256 p at decreasing
  rw [gammaAfter1030, at256] at decreasing
  have numeric := numeric1030 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 257 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 257 (.fill 258)))
  rw [oldBefore256, at256, literal, oldAfter1030, gammaAfter1030]
  exact numeric
theorem numeric1031 (p : Pattern) (guard : d381079 p = 1) (decreasing : d0 p < d47611 p) :
    d50823 p + d47611 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 256 p
  rw [at256] at beforeRange
  have afterRange := bonus_range 257 (HazardPattern.afterPattern 10000 p (.push 257 (.stay 258)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 257 (.stay 258))) (HazardPattern.afterPattern 10000 p (.push 257 (.stay 258))) ∧ bonus (HazardPattern.nextHero (.push 257 (.stay 258))) (HazardPattern.afterPattern 10000 p (.push 257 (.stay 258))) ≤ 2 at afterRange
  rw [gammaAfter1031] at afterRange
  have possibilities : (d47611 p = 1 ∧ d0 p = 0) ∨ (d47611 p = 2 ∧ d0 p = 0) ∨ (d47611 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39983 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108244 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro40008 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108245 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro40008 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108245 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1031 (p : Pattern) (guard : d381079 p = 1)
    (decreasing : bonus 257 (HazardPattern.afterPattern 10000 p (.push 257 (.stay 258))) < bonus 256 p) :
    NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 256 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 257 (.stay 258)) + NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 257 (.stay 258)))) + bonus 257 (HazardPattern.afterPattern 10000 p (.push 257 (.stay 258))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 257 (.stay 258)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 257 (.stay 258))) (HazardPattern.afterPattern 10000 p (.push 257 (.stay 258))) < bonus 256 p at decreasing
  rw [gammaAfter1031, at256] at decreasing
  have numeric := numeric1031 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 257 (.stay 258))) (HazardPattern.afterPattern 10000 p (.push 257 (.stay 258)))
  rw [oldBefore256, at256, literal, oldAfter1031, gammaAfter1031]
  exact numeric
theorem numeric1032 (p : Pattern) (guard : d380855 p = 1) (decreasing : d47561 p < d47611 p) :
    d50823 p + d47611 p ≤ (0 : Int) + d50823 p + d47561 p := by
  have beforeRange := bonus_range 256 p
  rw [at256] at beforeRange
  have afterRange := bonus_range 255 (HazardPattern.afterPattern 10000 p (.walk 255))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 255)) (HazardPattern.afterPattern 10000 p (.walk 255)) ∧ bonus (HazardPattern.nextHero (.walk 255)) (HazardPattern.afterPattern 10000 p (.walk 255)) ≤ 2 at afterRange
  rw [gammaAfter1032] at afterRange
  have possibilities : (d47611 p = 1 ∧ d47561 p = 0) ∨ (d47611 p = 2 ∧ d47561 p = 0) ∨ (d47611 p = 2 ∧ d47561 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39983 p pair.1
    have afterEq := eqIntro39921 p pair.2
    have combined := andIntro108246 p beforeEq guard
    have complete := andIntro108255 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro40008 p pair.1
    have afterEq := eqIntro39921 p pair.2
    have combined := andIntro108256 p beforeEq guard
    have complete := andIntro108257 p combined afterEq
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro40008 p pair.1
    have afterEq := eqIntro39938 p pair.2
    have combined := andIntro108256 p beforeEq guard
    have complete := andIntro108258 p combined afterEq
    have bound := compare41207 p complete
    omega
theorem local1032 (p : Pattern) (guard : d380855 p = 1)
    (decreasing : bonus 255 (HazardPattern.afterPattern 10000 p (.walk 255)) < bonus 256 p) :
    NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 256 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 255) + NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 255))) + bonus 255 (HazardPattern.afterPattern 10000 p (.walk 255)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 255) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 255)) (HazardPattern.afterPattern 10000 p (.walk 255)) < bonus 256 p at decreasing
  rw [gammaAfter1032, at256] at decreasing
  have numeric := numeric1032 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 255)) (HazardPattern.afterPattern 10000 p (.walk 255))
  rw [oldBefore256, at256, literal, oldAfter1032, gammaAfter1032]
  exact numeric
theorem numeric1033 (p : Pattern) (guard : d381086 p = 1) (decreasing : d381132 p < d47611 p) :
    d50823 p + d47611 p ≤ (1 : Int) + d50823 p + d381132 p := by
  have beforeRange := bonus_range 256 p
  rw [at256] at beforeRange
  have afterRange := bonus_range 255 (HazardPattern.afterPattern 10000 p (.push 255 (.fill 254)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 255 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 255 (.fill 254))) ∧ bonus (HazardPattern.nextHero (.push 255 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 255 (.fill 254))) ≤ 2 at afterRange
  rw [gammaAfter1033] at afterRange
  have possibilities : (d47611 p = 1 ∧ d381132 p = 0) ∨ (d47611 p = 2 ∧ d381132 p = 0) ∨ (d47611 p = 2 ∧ d381132 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39983 p pair.1
    have afterEq := eqIntro40016 p pair.2
    have combined := andIntro108265 p beforeEq guard
    have complete := andIntro108266 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro40008 p pair.1
    have afterEq := eqIntro40016 p pair.2
    have combined := andIntro108267 p beforeEq guard
    have complete := andIntro108266 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro40008 p pair.1
    have afterEq := eqIntro40024 p pair.2
    have combined := andIntro108267 p beforeEq guard
    have complete := andIntro108268 p combined afterEq
    have bound := compare49829 p complete
    omega
theorem local1033 (p : Pattern) (guard : d381086 p = 1)
    (decreasing : bonus 255 (HazardPattern.afterPattern 10000 p (.push 255 (.fill 254))) < bonus 256 p) :
    NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 256 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 255 (.fill 254)) + NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 255 (.fill 254)))) + bonus 255 (HazardPattern.afterPattern 10000 p (.push 255 (.fill 254))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 255 (.fill 254)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 255 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 255 (.fill 254))) < bonus 256 p at decreasing
  rw [gammaAfter1033, at256] at decreasing
  have numeric := numeric1033 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 255 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 255 (.fill 254)))
  rw [oldBefore256, at256, literal, oldAfter1033, gammaAfter1033]
  exact numeric
theorem numeric1034 (p : Pattern) (guard : d380710 p = 1) (decreasing : d0 p < d47611 p) :
    d50823 p + d47611 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 256 p
  rw [at256] at beforeRange
  have afterRange := bonus_range 255 (HazardPattern.afterPattern 10000 p (.push 255 (.stay 254)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 255 (.stay 254))) (HazardPattern.afterPattern 10000 p (.push 255 (.stay 254))) ∧ bonus (HazardPattern.nextHero (.push 255 (.stay 254))) (HazardPattern.afterPattern 10000 p (.push 255 (.stay 254))) ≤ 2 at afterRange
  rw [gammaAfter1034] at afterRange
  have possibilities : (d47611 p = 1 ∧ d0 p = 0) ∨ (d47611 p = 2 ∧ d0 p = 0) ∨ (d47611 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro39983 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108275 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro40008 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108276 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro40008 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108276 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1034 (p : Pattern) (guard : d380710 p = 1)
    (decreasing : bonus 255 (HazardPattern.afterPattern 10000 p (.push 255 (.stay 254))) < bonus 256 p) :
    NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 256 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 255 (.stay 254)) + NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 255 (.stay 254)))) + bonus 255 (HazardPattern.afterPattern 10000 p (.push 255 (.stay 254))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 255 (.stay 254)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 255 (.stay 254))) (HazardPattern.afterPattern 10000 p (.push 255 (.stay 254))) < bonus 256 p at decreasing
  rw [gammaAfter1034, at256] at decreasing
  have numeric := numeric1034 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 255 (.stay 254))) (HazardPattern.afterPattern 10000 p (.push 255 (.stay 254)))
  rw [oldBefore256, at256, literal, oldAfter1034, gammaAfter1034]
  exact numeric
theorem numeric1035 (p : Pattern) (guard : d381230 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (0 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 257 p
  rw [at257] at beforeRange
  have afterRange := bonus_range 258 (HazardPattern.afterPattern 10000 p (.walk 258))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 258)) (HazardPattern.afterPattern 10000 p (.walk 258)) ∧ bonus (HazardPattern.nextHero (.walk 258)) (HazardPattern.afterPattern 10000 p (.walk 258)) ≤ 2 at afterRange
  rw [gammaAfter1035] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108277 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108277 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108277 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare41207 p complete
    omega
theorem local1035 (p : Pattern) (guard : d381230 p = 1)
    (decreasing : bonus 258 (HazardPattern.afterPattern 10000 p (.walk 258)) < bonus 257 p) :
    NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 257 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 258) + NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 258))) + bonus 258 (HazardPattern.afterPattern 10000 p (.walk 258)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 258) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 258)) (HazardPattern.afterPattern 10000 p (.walk 258)) < bonus 257 p at decreasing
  rw [gammaAfter1035, at257] at decreasing
  have numeric := numeric1035 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 258)) (HazardPattern.afterPattern 10000 p (.walk 258))
  rw [oldBefore257, at257, literal, oldAfter1035, gammaAfter1035]
  exact numeric
theorem numeric1036 (p : Pattern) (guard : d381239 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 257 p
  rw [at257] at beforeRange
  have afterRange := bonus_range 258 (HazardPattern.afterPattern 10000 p (.push 258 (.fill 259)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 258 (.fill 259))) (HazardPattern.afterPattern 10000 p (.push 258 (.fill 259))) ∧ bonus (HazardPattern.nextHero (.push 258 (.fill 259))) (HazardPattern.afterPattern 10000 p (.push 258 (.fill 259))) ≤ 2 at afterRange
  rw [gammaAfter1036] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108278 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108278 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108278 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1036 (p : Pattern) (guard : d381239 p = 1)
    (decreasing : bonus 258 (HazardPattern.afterPattern 10000 p (.push 258 (.fill 259))) < bonus 257 p) :
    NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 257 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 258 (.fill 259)) + NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 258 (.fill 259)))) + bonus 258 (HazardPattern.afterPattern 10000 p (.push 258 (.fill 259))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 258 (.fill 259)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 258 (.fill 259))) (HazardPattern.afterPattern 10000 p (.push 258 (.fill 259))) < bonus 257 p at decreasing
  rw [gammaAfter1036, at257] at decreasing
  have numeric := numeric1036 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 258 (.fill 259))) (HazardPattern.afterPattern 10000 p (.push 258 (.fill 259)))
  rw [oldBefore257, at257, literal, oldAfter1036, gammaAfter1036]
  exact numeric
theorem numeric1037 (p : Pattern) (guard : d381243 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 257 p
  rw [at257] at beforeRange
  have afterRange := bonus_range 258 (HazardPattern.afterPattern 10000 p (.push 258 (.stay 259)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 258 (.stay 259))) (HazardPattern.afterPattern 10000 p (.push 258 (.stay 259))) ∧ bonus (HazardPattern.nextHero (.push 258 (.stay 259))) (HazardPattern.afterPattern 10000 p (.push 258 (.stay 259))) ≤ 2 at afterRange
  rw [gammaAfter1037] at afterRange
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
theorem local1037 (p : Pattern) (guard : d381243 p = 1)
    (decreasing : bonus 258 (HazardPattern.afterPattern 10000 p (.push 258 (.stay 259))) < bonus 257 p) :
    NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 257 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 258 (.stay 259)) + NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 258 (.stay 259)))) + bonus 258 (HazardPattern.afterPattern 10000 p (.push 258 (.stay 259))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 258 (.stay 259)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 258 (.stay 259))) (HazardPattern.afterPattern 10000 p (.push 258 (.stay 259))) < bonus 257 p at decreasing
  rw [gammaAfter1037, at257] at decreasing
  have numeric := numeric1037 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 258 (.stay 259))) (HazardPattern.afterPattern 10000 p (.push 258 (.stay 259)))
  rw [oldBefore257, at257, literal, oldAfter1037, gammaAfter1037]
  exact numeric
theorem numeric1038 (p : Pattern) (guard : d381066 p = 1) (decreasing : d47611 p < d0 p) :
    d50823 p + d0 p ≤ (0 : Int) + d50823 p + d47611 p := by
  have beforeRange := bonus_range 257 p
  rw [at257] at beforeRange
  have afterRange := bonus_range 256 (HazardPattern.afterPattern 10000 p (.walk 256))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 256)) (HazardPattern.afterPattern 10000 p (.walk 256)) ∧ bonus (HazardPattern.nextHero (.walk 256)) (HazardPattern.afterPattern 10000 p (.walk 256)) ≤ 2 at afterRange
  rw [gammaAfter1038] at afterRange
  have possibilities : (d0 p = 1 ∧ d47611 p = 0) ∨ (d0 p = 2 ∧ d47611 p = 0) ∨ (d0 p = 2 ∧ d47611 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro39973 p pair.2
    have combined := andIntro108229 p beforeEq guard
    have complete := andIntro108131 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro39973 p pair.2
    have combined := andIntro108229 p beforeEq guard
    have complete := andIntro108131 p combined afterEq
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro39983 p pair.2
    have combined := andIntro108229 p beforeEq guard
    have complete := andIntro108132 p combined afterEq
    have bound := compare41207 p complete
    omega
theorem local1038 (p : Pattern) (guard : d381066 p = 1)
    (decreasing : bonus 256 (HazardPattern.afterPattern 10000 p (.walk 256)) < bonus 257 p) :
    NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 257 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 256) + NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 256))) + bonus 256 (HazardPattern.afterPattern 10000 p (.walk 256)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 256) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 256)) (HazardPattern.afterPattern 10000 p (.walk 256)) < bonus 257 p at decreasing
  rw [gammaAfter1038, at257] at decreasing
  have numeric := numeric1038 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 256)) (HazardPattern.afterPattern 10000 p (.walk 256))
  rw [oldBefore257, at257, literal, oldAfter1038, gammaAfter1038]
  exact numeric
theorem numeric1039 (p : Pattern) (guard : d381250 p = 1) (decreasing : d381297 p < d0 p) :
    d50823 p + d0 p ≤ (1 : Int) + d50823 p + d381297 p := by
  have beforeRange := bonus_range 257 p
  rw [at257] at beforeRange
  have afterRange := bonus_range 256 (HazardPattern.afterPattern 10000 p (.push 256 (.fill 255)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 256 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 256 (.fill 255))) ∧ bonus (HazardPattern.nextHero (.push 256 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 256 (.fill 255))) ≤ 2 at afterRange
  rw [gammaAfter1039] at afterRange
  have possibilities : (d0 p = 1 ∧ d381297 p = 0) ∨ (d0 p = 2 ∧ d381297 p = 0) ∨ (d0 p = 2 ∧ d381297 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro40033 p pair.2
    have combined := andIntro108280 p beforeEq guard
    have complete := andIntro108281 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro40033 p pair.2
    have combined := andIntro108280 p beforeEq guard
    have complete := andIntro108281 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro40034 p pair.2
    have combined := andIntro108280 p beforeEq guard
    have complete := andIntro108282 p combined afterEq
    have bound := compare49829 p complete
    omega
theorem local1039 (p : Pattern) (guard : d381250 p = 1)
    (decreasing : bonus 256 (HazardPattern.afterPattern 10000 p (.push 256 (.fill 255))) < bonus 257 p) :
    NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 257 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 256 (.fill 255)) + NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 256 (.fill 255)))) + bonus 256 (HazardPattern.afterPattern 10000 p (.push 256 (.fill 255))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 256 (.fill 255)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 256 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 256 (.fill 255))) < bonus 257 p at decreasing
  rw [gammaAfter1039, at257] at decreasing
  have numeric := numeric1039 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 256 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 256 (.fill 255)))
  rw [oldBefore257, at257, literal, oldAfter1039, gammaAfter1039]
  exact numeric
theorem numeric1040 (p : Pattern) (guard : d380918 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 257 p
  rw [at257] at beforeRange
  have afterRange := bonus_range 256 (HazardPattern.afterPattern 10000 p (.push 256 (.stay 255)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 256 (.stay 255))) (HazardPattern.afterPattern 10000 p (.push 256 (.stay 255))) ∧ bonus (HazardPattern.nextHero (.push 256 (.stay 255))) (HazardPattern.afterPattern 10000 p (.push 256 (.stay 255))) ≤ 2 at afterRange
  rw [gammaAfter1040] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108283 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108283 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108283 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1040 (p : Pattern) (guard : d380918 p = 1)
    (decreasing : bonus 256 (HazardPattern.afterPattern 10000 p (.push 256 (.stay 255))) < bonus 257 p) :
    NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 257 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 256 (.stay 255)) + NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 256 (.stay 255)))) + bonus 256 (HazardPattern.afterPattern 10000 p (.push 256 (.stay 255))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 256 (.stay 255)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 256 (.stay 255))) (HazardPattern.afterPattern 10000 p (.push 256 (.stay 255))) < bonus 257 p at decreasing
  rw [gammaAfter1040, at257] at decreasing
  have numeric := numeric1040 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 256 (.stay 255))) (HazardPattern.afterPattern 10000 p (.push 256 (.stay 255)))
  rw [oldBefore257, at257, literal, oldAfter1040, gammaAfter1040]
  exact numeric
theorem numeric1041 (p : Pattern) (guard : d381350 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (0 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 258 p
  rw [at258] at beforeRange
  have afterRange := bonus_range 259 (HazardPattern.afterPattern 10000 p (.walk 259))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 259)) (HazardPattern.afterPattern 10000 p (.walk 259)) ∧ bonus (HazardPattern.nextHero (.walk 259)) (HazardPattern.afterPattern 10000 p (.walk 259)) ≤ 2 at afterRange
  rw [gammaAfter1041] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108284 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108284 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108284 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare41207 p complete
    omega
theorem local1041 (p : Pattern) (guard : d381350 p = 1)
    (decreasing : bonus 259 (HazardPattern.afterPattern 10000 p (.walk 259)) < bonus 258 p) :
    NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 258 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 259) + NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 259))) + bonus 259 (HazardPattern.afterPattern 10000 p (.walk 259)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 259) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 259)) (HazardPattern.afterPattern 10000 p (.walk 259)) < bonus 258 p at decreasing
  rw [gammaAfter1041, at258] at decreasing
  have numeric := numeric1041 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 259)) (HazardPattern.afterPattern 10000 p (.walk 259))
  rw [oldBefore258, at258, literal, oldAfter1041, gammaAfter1041]
  exact numeric
theorem numeric1042 (p : Pattern) (guard : d381359 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 258 p
  rw [at258] at beforeRange
  have afterRange := bonus_range 259 (HazardPattern.afterPattern 10000 p (.push 259 (.fill 260)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 259 (.fill 260))) (HazardPattern.afterPattern 10000 p (.push 259 (.fill 260))) ∧ bonus (HazardPattern.nextHero (.push 259 (.fill 260))) (HazardPattern.afterPattern 10000 p (.push 259 (.fill 260))) ≤ 2 at afterRange
  rw [gammaAfter1042] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108285 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108285 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108285 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1042 (p : Pattern) (guard : d381359 p = 1)
    (decreasing : bonus 259 (HazardPattern.afterPattern 10000 p (.push 259 (.fill 260))) < bonus 258 p) :
    NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 258 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 259 (.fill 260)) + NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 259 (.fill 260)))) + bonus 259 (HazardPattern.afterPattern 10000 p (.push 259 (.fill 260))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 259 (.fill 260)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 259 (.fill 260))) (HazardPattern.afterPattern 10000 p (.push 259 (.fill 260))) < bonus 258 p at decreasing
  rw [gammaAfter1042, at258] at decreasing
  have numeric := numeric1042 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 259 (.fill 260))) (HazardPattern.afterPattern 10000 p (.push 259 (.fill 260)))
  rw [oldBefore258, at258, literal, oldAfter1042, gammaAfter1042]
  exact numeric
theorem numeric1043 (p : Pattern) (guard : d381363 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 258 p
  rw [at258] at beforeRange
  have afterRange := bonus_range 259 (HazardPattern.afterPattern 10000 p (.push 259 (.stay 260)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 259 (.stay 260))) (HazardPattern.afterPattern 10000 p (.push 259 (.stay 260))) ∧ bonus (HazardPattern.nextHero (.push 259 (.stay 260))) (HazardPattern.afterPattern 10000 p (.push 259 (.stay 260))) ≤ 2 at afterRange
  rw [gammaAfter1043] at afterRange
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
theorem local1043 (p : Pattern) (guard : d381363 p = 1)
    (decreasing : bonus 259 (HazardPattern.afterPattern 10000 p (.push 259 (.stay 260))) < bonus 258 p) :
    NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 258 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 259 (.stay 260)) + NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 259 (.stay 260)))) + bonus 259 (HazardPattern.afterPattern 10000 p (.push 259 (.stay 260))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 259 (.stay 260)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 259 (.stay 260))) (HazardPattern.afterPattern 10000 p (.push 259 (.stay 260))) < bonus 258 p at decreasing
  rw [gammaAfter1043, at258] at decreasing
  have numeric := numeric1043 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 259 (.stay 260))) (HazardPattern.afterPattern 10000 p (.push 259 (.stay 260)))
  rw [oldBefore258, at258, literal, oldAfter1043, gammaAfter1043]
  exact numeric
theorem numeric1044 (p : Pattern) (guard : d381230 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (0 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 258 p
  rw [at258] at beforeRange
  have afterRange := bonus_range 257 (HazardPattern.afterPattern 10000 p (.walk 257))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 257)) (HazardPattern.afterPattern 10000 p (.walk 257)) ∧ bonus (HazardPattern.nextHero (.walk 257)) (HazardPattern.afterPattern 10000 p (.walk 257)) ≤ 2 at afterRange
  rw [gammaAfter1044] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108277 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108277 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108277 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare41207 p complete
    omega
theorem local1044 (p : Pattern) (guard : d381230 p = 1)
    (decreasing : bonus 257 (HazardPattern.afterPattern 10000 p (.walk 257)) < bonus 258 p) :
    NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 258 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 257) + NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 257))) + bonus 257 (HazardPattern.afterPattern 10000 p (.walk 257)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 257) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 257)) (HazardPattern.afterPattern 10000 p (.walk 257)) < bonus 258 p at decreasing
  rw [gammaAfter1044, at258] at decreasing
  have numeric := numeric1044 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 257)) (HazardPattern.afterPattern 10000 p (.walk 257))
  rw [oldBefore258, at258, literal, oldAfter1044, gammaAfter1044]
  exact numeric
theorem numeric1045 (p : Pattern) (guard : d381370 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 258 p
  rw [at258] at beforeRange
  have afterRange := bonus_range 257 (HazardPattern.afterPattern 10000 p (.push 257 (.fill 256)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 257 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 257 (.fill 256))) ∧ bonus (HazardPattern.nextHero (.push 257 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 257 (.fill 256))) ≤ 2 at afterRange
  rw [gammaAfter1045] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108287 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108287 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108287 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1045 (p : Pattern) (guard : d381370 p = 1)
    (decreasing : bonus 257 (HazardPattern.afterPattern 10000 p (.push 257 (.fill 256))) < bonus 258 p) :
    NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 258 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 257 (.fill 256)) + NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 257 (.fill 256)))) + bonus 257 (HazardPattern.afterPattern 10000 p (.push 257 (.fill 256))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 257 (.fill 256)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 257 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 257 (.fill 256))) < bonus 258 p at decreasing
  rw [gammaAfter1045, at258] at decreasing
  have numeric := numeric1045 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 257 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 257 (.fill 256)))
  rw [oldBefore258, at258, literal, oldAfter1045, gammaAfter1045]
  exact numeric
theorem numeric1046 (p : Pattern) (guard : d381079 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 258 p
  rw [at258] at beforeRange
  have afterRange := bonus_range 257 (HazardPattern.afterPattern 10000 p (.push 257 (.stay 256)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 257 (.stay 256))) (HazardPattern.afterPattern 10000 p (.push 257 (.stay 256))) ∧ bonus (HazardPattern.nextHero (.push 257 (.stay 256))) (HazardPattern.afterPattern 10000 p (.push 257 (.stay 256))) ≤ 2 at afterRange
  rw [gammaAfter1046] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108245 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108245 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108245 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1046 (p : Pattern) (guard : d381079 p = 1)
    (decreasing : bonus 257 (HazardPattern.afterPattern 10000 p (.push 257 (.stay 256))) < bonus 258 p) :
    NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 258 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 257 (.stay 256)) + NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 257 (.stay 256)))) + bonus 257 (HazardPattern.afterPattern 10000 p (.push 257 (.stay 256))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 257 (.stay 256)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 257 (.stay 256))) (HazardPattern.afterPattern 10000 p (.push 257 (.stay 256))) < bonus 258 p at decreasing
  rw [gammaAfter1046, at258] at decreasing
  have numeric := numeric1046 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 257 (.stay 256))) (HazardPattern.afterPattern 10000 p (.push 257 (.stay 256)))
  rw [oldBefore258, at258, literal, oldAfter1046, gammaAfter1046]
  exact numeric
theorem numeric1047 (p : Pattern) (guard : d381376 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (0 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 259 p
  rw [at259] at beforeRange
  have afterRange := bonus_range 260 (HazardPattern.afterPattern 10000 p (.walk 260))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 260)) (HazardPattern.afterPattern 10000 p (.walk 260)) ∧ bonus (HazardPattern.nextHero (.walk 260)) (HazardPattern.afterPattern 10000 p (.walk 260)) ≤ 2 at afterRange
  rw [gammaAfter1047] at afterRange
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
theorem local1047 (p : Pattern) (guard : d381376 p = 1)
    (decreasing : bonus 260 (HazardPattern.afterPattern 10000 p (.walk 260)) < bonus 259 p) :
    NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 259 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 260) + NetHack.Sokoban22Refined85.bonus 260 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 260))) + bonus 260 (HazardPattern.afterPattern 10000 p (.walk 260)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 260) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 260)) (HazardPattern.afterPattern 10000 p (.walk 260)) < bonus 259 p at decreasing
  rw [gammaAfter1047, at259] at decreasing
  have numeric := numeric1047 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 260)) (HazardPattern.afterPattern 10000 p (.walk 260))
  rw [oldBefore259, at259, literal, oldAfter1047, gammaAfter1047]
  exact numeric
theorem numeric1048 (p : Pattern) (guard : d381350 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (0 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 259 p
  rw [at259] at beforeRange
  have afterRange := bonus_range 258 (HazardPattern.afterPattern 10000 p (.walk 258))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 258)) (HazardPattern.afterPattern 10000 p (.walk 258)) ∧ bonus (HazardPattern.nextHero (.walk 258)) (HazardPattern.afterPattern 10000 p (.walk 258)) ≤ 2 at afterRange
  rw [gammaAfter1048] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108284 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108284 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108284 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare41207 p complete
    omega
theorem local1048 (p : Pattern) (guard : d381350 p = 1)
    (decreasing : bonus 258 (HazardPattern.afterPattern 10000 p (.walk 258)) < bonus 259 p) :
    NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 259 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 258) + NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 258))) + bonus 258 (HazardPattern.afterPattern 10000 p (.walk 258)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 258) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 258)) (HazardPattern.afterPattern 10000 p (.walk 258)) < bonus 259 p at decreasing
  rw [gammaAfter1048, at259] at decreasing
  have numeric := numeric1048 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 258)) (HazardPattern.afterPattern 10000 p (.walk 258))
  rw [oldBefore259, at259, literal, oldAfter1048, gammaAfter1048]
  exact numeric
theorem numeric1049 (p : Pattern) (guard : d381383 p = 1) (decreasing : d0 p < d0 p) :
    d50823 p + d0 p ≤ (1 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 259 p
  rw [at259] at beforeRange
  have afterRange := bonus_range 258 (HazardPattern.afterPattern 10000 p (.push 258 (.fill 257)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 258 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 258 (.fill 257))) ∧ bonus (HazardPattern.nextHero (.push 258 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 258 (.fill 257))) ≤ 2 at afterRange
  rw [gammaAfter1049] at afterRange
  have possibilities : (d0 p = 1 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 0) ∨ (d0 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro1384 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108289 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare49829 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro108289 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro3287 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro108289 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare49829 p complete
    omega
theorem local1049 (p : Pattern) (guard : d381383 p = 1)
    (decreasing : bonus 258 (HazardPattern.afterPattern 10000 p (.push 258 (.fill 257))) < bonus 259 p) :
    NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 259 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 258 (.fill 257)) + NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 258 (.fill 257)))) + bonus 258 (HazardPattern.afterPattern 10000 p (.push 258 (.fill 257))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 258 (.fill 257)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 258 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 258 (.fill 257))) < bonus 259 p at decreasing
  rw [gammaAfter1049, at259] at decreasing
  have numeric := numeric1049 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 258 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 258 (.fill 257)))
  rw [oldBefore259, at259, literal, oldAfter1049, gammaAfter1049]
  exact numeric
end NetHack.Soko22Hazard87
