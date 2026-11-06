import NetHack.Soko22Hazard87.Numeric012
import NetHack.Soko22Hazard87.AndIntroBlocks0412
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem numeric910 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 215 p
  rw [at215] at beforeRange
  have afterRange := bonus_range 194 (HazardPattern.afterPattern 10000 p (.walk 194))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) ∧ bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) ≤ 2 at afterRange
  rw [gammaAfter910] at afterRange
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
theorem local910 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 194 (HazardPattern.afterPattern 10000 p (.walk 194)) < bonus 215 p) :
    NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 215 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 194) + NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 194))) + bonus 194 (HazardPattern.afterPattern 10000 p (.walk 194)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 194) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) < bonus 215 p at decreasing
  rw [gammaAfter910, at215] at decreasing
  have numeric := numeric910 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194))
  rw [oldBefore215, at215, literal, oldAfter910, gammaAfter910]
  exact numeric
theorem numeric911 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 215 p
  rw [at215] at beforeRange
  have afterRange := bonus_range 192 (HazardPattern.afterPattern 10000 p (.walk 192))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ∧ bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) ≤ 2 at afterRange
  rw [gammaAfter911] at afterRange
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
theorem local911 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 215 p) :
    NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 215 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 192) + NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 192))) + bonus 192 (HazardPattern.afterPattern 10000 p (.walk 192)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 192) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) < bonus 215 p at decreasing
  rw [gammaAfter911, at215] at decreasing
  have numeric := numeric911 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192))
  rw [oldBefore215, at215, literal, oldAfter911, gammaAfter911]
  exact numeric
theorem numeric912 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 216 p
  rw [at216] at beforeRange
  have afterRange := bonus_range 194 (HazardPattern.afterPattern 10000 p (.walk 194))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) ∧ bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) ≤ 2 at afterRange
  rw [gammaAfter912] at afterRange
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
theorem local912 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 194 (HazardPattern.afterPattern 10000 p (.walk 194)) < bonus 216 p) :
    NetHack.Sokoban22Refined85.bonus 216 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 216 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 194) + NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 194))) + bonus 194 (HazardPattern.afterPattern 10000 p (.walk 194)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 194) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) < bonus 216 p at decreasing
  rw [gammaAfter912, at216] at decreasing
  have numeric := numeric912 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194))
  rw [oldBefore216, at216, literal, oldAfter912, gammaAfter912]
  exact numeric
theorem numeric913 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 216 p
  rw [at216] at beforeRange
  have afterRange := bonus_range 194 (HazardPattern.afterPattern 10000 p (.push 194 (.stay 172)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 194 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 194 (.stay 172))) ∧ bonus (HazardPattern.nextHero (.push 194 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 194 (.stay 172))) ≤ 2 at afterRange
  rw [gammaAfter913] at afterRange
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
theorem local913 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 194 (HazardPattern.afterPattern 10000 p (.push 194 (.stay 172))) < bonus 216 p) :
    NetHack.Sokoban22Refined85.bonus 216 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 216 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 194 (.stay 172)) + NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 194 (.stay 172)))) + bonus 194 (HazardPattern.afterPattern 10000 p (.push 194 (.stay 172))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 194 (.stay 172)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 194 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 194 (.stay 172))) < bonus 216 p at decreasing
  rw [gammaAfter913, at216] at decreasing
  have numeric := numeric913 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 194 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 194 (.stay 172)))
  rw [oldBefore216, at216, literal, oldAfter913, gammaAfter913]
  exact numeric
theorem numeric914 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 216 p
  rw [at216] at beforeRange
  have afterRange := bonus_range 215 (HazardPattern.afterPattern 10000 p (.walk 215))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) ∧ bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) ≤ 2 at afterRange
  rw [gammaAfter914] at afterRange
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
theorem local914 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 215 (HazardPattern.afterPattern 10000 p (.walk 215)) < bonus 216 p) :
    NetHack.Sokoban22Refined85.bonus 216 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 216 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 215) + NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 215))) + bonus 215 (HazardPattern.afterPattern 10000 p (.walk 215)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 215) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215)) < bonus 216 p at decreasing
  rw [gammaAfter914, at216] at decreasing
  have numeric := numeric914 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 215)) (HazardPattern.afterPattern 10000 p (.walk 215))
  rw [oldBefore216, at216, literal, oldAfter914, gammaAfter914]
  exact numeric
theorem numeric915 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 216 p
  rw [at216] at beforeRange
  have afterRange := bonus_range 215 (HazardPattern.afterPattern 10000 p (.push 215 (.stay 214)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 215 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 215 (.stay 214))) ∧ bonus (HazardPattern.nextHero (.push 215 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 215 (.stay 214))) ≤ 2 at afterRange
  rw [gammaAfter915] at afterRange
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
theorem local915 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 215 (HazardPattern.afterPattern 10000 p (.push 215 (.stay 214))) < bonus 216 p) :
    NetHack.Sokoban22Refined85.bonus 216 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 216 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 215 (.stay 214)) + NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 215 (.stay 214)))) + bonus 215 (HazardPattern.afterPattern 10000 p (.push 215 (.stay 214))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 215 (.stay 214)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 215 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 215 (.stay 214))) < bonus 216 p at decreasing
  rw [gammaAfter915, at216] at decreasing
  have numeric := numeric915 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 215 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 215 (.stay 214)))
  rw [oldBefore216, at216, literal, oldAfter915, gammaAfter915]
  exact numeric
theorem numeric916 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 216 p
  rw [at216] at beforeRange
  have afterRange := bonus_range 193 (HazardPattern.afterPattern 10000 p (.walk 193))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ∧ bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) ≤ 2 at afterRange
  rw [gammaAfter916] at afterRange
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
theorem local916 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 216 p) :
    NetHack.Sokoban22Refined85.bonus 216 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 216 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 193) + NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 193))) + bonus 193 (HazardPattern.afterPattern 10000 p (.walk 193)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 193) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) < bonus 216 p at decreasing
  rw [gammaAfter916, at216] at decreasing
  have numeric := numeric916 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193))
  rw [oldBefore216, at216, literal, oldAfter916, gammaAfter916]
  exact numeric
theorem numeric917 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 218 p
  rw [at218] at beforeRange
  have afterRange := bonus_range 240 (HazardPattern.afterPattern 10000 p (.walk 240))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 240)) (HazardPattern.afterPattern 10000 p (.walk 240)) ∧ bonus (HazardPattern.nextHero (.walk 240)) (HazardPattern.afterPattern 10000 p (.walk 240)) ≤ 2 at afterRange
  rw [gammaAfter917] at afterRange
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
theorem local917 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 240 (HazardPattern.afterPattern 10000 p (.walk 240)) < bonus 218 p) :
    NetHack.Sokoban22Refined85.bonus 218 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 218 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 240) + NetHack.Sokoban22Refined85.bonus 240 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 240))) + bonus 240 (HazardPattern.afterPattern 10000 p (.walk 240)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 240) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 240)) (HazardPattern.afterPattern 10000 p (.walk 240)) < bonus 218 p at decreasing
  rw [gammaAfter917, at218] at decreasing
  have numeric := numeric917 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 240)) (HazardPattern.afterPattern 10000 p (.walk 240))
  rw [oldBefore218, at218, literal, oldAfter917, gammaAfter917]
  exact numeric
theorem numeric918 (p : Pattern) (guard : d0 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (1 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 218 p
  rw [at218] at beforeRange
  have afterRange := bonus_range 240 (HazardPattern.afterPattern 10000 p (.push 240 (.stay 262)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 240 (.stay 262))) (HazardPattern.afterPattern 10000 p (.push 240 (.stay 262))) ∧ bonus (HazardPattern.nextHero (.push 240 (.stay 262))) (HazardPattern.afterPattern 10000 p (.push 240 (.stay 262))) ≤ 2 at afterRange
  rw [gammaAfter918] at afterRange
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
theorem local918 (p : Pattern) (guard : d0 p = 1)
    (decreasing : bonus 240 (HazardPattern.afterPattern 10000 p (.push 240 (.stay 262))) < bonus 218 p) :
    NetHack.Sokoban22Refined85.bonus 218 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 218 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 240 (.stay 262)) + NetHack.Sokoban22Refined85.bonus 240 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 240 (.stay 262)))) + bonus 240 (HazardPattern.afterPattern 10000 p (.push 240 (.stay 262))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 240 (.stay 262)) = (1 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 240 (.stay 262))) (HazardPattern.afterPattern 10000 p (.push 240 (.stay 262))) < bonus 218 p at decreasing
  rw [gammaAfter918, at218] at decreasing
  have numeric := numeric918 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 240 (.stay 262))) (HazardPattern.afterPattern 10000 p (.push 240 (.stay 262)))
  rw [oldBefore218, at218, literal, oldAfter918, gammaAfter918]
  exact numeric
theorem numeric919 (p : Pattern) (guard : d236582 p = 1) (decreasing : d25101 p < d30634 p) :
    d47866 p + d30634 p ≤ (0 : Int) + d47866 p + d25101 p := by
  have beforeRange := bonus_range 223 p
  rw [at223] at beforeRange
  have afterRange := bonus_range 201 (HazardPattern.afterPattern 10000 p (.walk 201))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) ∧ bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) ≤ 2 at afterRange
  rw [gammaAfter919] at afterRange
  have possibilities : (d30634 p = 1 ∧ d25101 p = 0) ∨ (d30634 p = 2 ∧ d25101 p = 0) ∨ (d30634 p = 2 ∧ d25101 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro23933 p pair.1
    have afterEq := eqIntro20211 p pair.2
    have combined := andIntro70705 p guard beforeEq
    have complete := andIntro70884 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro20211 p pair.2
    have combined := andIntro70912 p guard beforeEq
    have complete := andIntro70938 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro20354 p pair.2
    have combined := andIntro70912 p guard beforeEq
    have complete := andIntro70964 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local919 (p : Pattern) (guard : d236582 p = 1)
    (decreasing : bonus 201 (HazardPattern.afterPattern 10000 p (.walk 201)) < bonus 223 p) :
    NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 223 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 201) + NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 201))) + bonus 201 (HazardPattern.afterPattern 10000 p (.walk 201)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 201) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) < bonus 223 p at decreasing
  rw [gammaAfter919, at223] at decreasing
  have numeric := numeric919 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201))
  rw [oldBefore223, at223, literal, oldAfter919, gammaAfter919]
  exact numeric
theorem numeric920 (p : Pattern) (guard : d279951 p = 1) (decreasing : d40148 p < d30634 p) :
    d47866 p + d30634 p ≤ (0 : Int) + d47866 p + d40148 p := by
  have beforeRange := bonus_range 223 p
  rw [at223] at beforeRange
  have afterRange := bonus_range 245 (HazardPattern.afterPattern 10000 p (.walk 245))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 245)) (HazardPattern.afterPattern 10000 p (.walk 245)) ∧ bonus (HazardPattern.nextHero (.walk 245)) (HazardPattern.afterPattern 10000 p (.walk 245)) ≤ 2 at afterRange
  rw [gammaAfter920] at afterRange
  have possibilities : (d30634 p = 1 ∧ d40148 p = 0) ∨ (d30634 p = 2 ∧ d40148 p = 0) ∨ (d30634 p = 2 ∧ d40148 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro23933 p pair.1
    have afterEq := eqIntro28987 p pair.2
    have combined := andIntro70965 p beforeEq guard
    have complete := andIntro71202 p combined afterEq
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro28987 p pair.2
    have combined := andIntro71203 p beforeEq guard
    have complete := andIntro71241 p combined afterEq
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro29076 p pair.2
    have combined := andIntro71203 p beforeEq guard
    have complete := andIntro71279 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local920 (p : Pattern) (guard : d279951 p = 1)
    (decreasing : bonus 245 (HazardPattern.afterPattern 10000 p (.walk 245)) < bonus 223 p) :
    NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 223 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 245) + NetHack.Sokoban22Refined85.bonus 245 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 245))) + bonus 245 (HazardPattern.afterPattern 10000 p (.walk 245)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 245) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 245)) (HazardPattern.afterPattern 10000 p (.walk 245)) < bonus 223 p at decreasing
  rw [gammaAfter920, at223] at decreasing
  have numeric := numeric920 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 245)) (HazardPattern.afterPattern 10000 p (.walk 245))
  rw [oldBefore223, at223, literal, oldAfter920, gammaAfter920]
  exact numeric
theorem numeric921 (p : Pattern) (guard : d241830 p = 1) (decreasing : d33212 p < d30634 p) :
    d47866 p + d30634 p ≤ (0 : Int) + d50101 p + d33212 p := by
  have beforeRange := bonus_range 223 p
  rw [at223] at beforeRange
  have afterRange := bonus_range 224 (HazardPattern.afterPattern 10000 p (.walk 224))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ∧ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ≤ 2 at afterRange
  rw [gammaAfter921] at afterRange
  have possibilities : (d30634 p = 1 ∧ d33212 p = 0) ∨ (d30634 p = 2 ∧ d33212 p = 0) ∨ (d30634 p = 2 ∧ d33212 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro23933 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro71607 p beforeEq guard
    have complete := andIntro71929 p afterEq combined
    have bound := compare28889 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro71961 p guard beforeEq
    have complete := andIntro72005 p afterEq combined
    have bound := compare28890 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro24937 p pair.2
    have combined := andIntro71961 p guard beforeEq
    have complete := andIntro72049 p afterEq combined
    have bound := compare28889 p complete
    omega
theorem local921 (p : Pattern) (guard : d241830 p = 1)
    (decreasing : bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 223 p) :
    NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 223 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 224) + NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 224))) + bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 224) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 223 p at decreasing
  rw [gammaAfter921, at223] at decreasing
  have numeric := numeric921 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224))
  rw [oldBefore223, at223, literal, oldAfter921, gammaAfter921]
  exact numeric
theorem numeric922 (p : Pattern) (guard : d282284 p = 1) (decreasing : d284334 p < d30634 p) :
    d47866 p + d30634 p ≤ (0 : Int) + d47866 p + d284334 p := by
  have beforeRange := bonus_range 223 p
  rw [at223] at beforeRange
  have afterRange := bonus_range 224 (HazardPattern.afterPattern 10000 p (.push 224 (.stay 225)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 224 (.stay 225))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 225))) ∧ bonus (HazardPattern.nextHero (.push 224 (.stay 225))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 225))) ≤ 2 at afterRange
  rw [gammaAfter922] at afterRange
  have possibilities : (d30634 p = 1 ∧ d284334 p = 0) ∨ (d30634 p = 2 ∧ d284334 p = 0) ∨ (d30634 p = 2 ∧ d284334 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro23933 p pair.1
    have afterEq := eqIntro29463 p pair.2
    have combined := andIntro72420 p beforeEq guard
    have complete := andIntro72706 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro29463 p pair.2
    have combined := andIntro72739 p beforeEq guard
    have complete := andIntro72783 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro29607 p pair.2
    have combined := andIntro72739 p beforeEq guard
    have complete := andIntro72827 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local922 (p : Pattern) (guard : d282284 p = 1)
    (decreasing : bonus 224 (HazardPattern.afterPattern 10000 p (.push 224 (.stay 225))) < bonus 223 p) :
    NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 223 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 224 (.stay 225)) + NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 224 (.stay 225)))) + bonus 224 (HazardPattern.afterPattern 10000 p (.push 224 (.stay 225))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 224 (.stay 225)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 224 (.stay 225))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 225))) < bonus 223 p at decreasing
  rw [gammaAfter922, at223] at decreasing
  have numeric := numeric922 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 224 (.stay 225))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 225)))
  rw [oldBefore223, at223, literal, oldAfter922, gammaAfter922]
  exact numeric
theorem numeric923 (p : Pattern) (guard : d266246 p = 1) (decreasing : d27480 p < d30634 p) :
    d47866 p + d30634 p ≤ (0 : Int) + d47866 p + d27480 p := by
  have beforeRange := bonus_range 223 p
  rw [at223] at beforeRange
  have afterRange := bonus_range 202 (HazardPattern.afterPattern 10000 p (.walk 202))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) ∧ bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) ≤ 2 at afterRange
  rw [gammaAfter923] at afterRange
  have possibilities : (d30634 p = 1 ∧ d27480 p = 0) ∨ (d30634 p = 2 ∧ d27480 p = 0) ∨ (d30634 p = 2 ∧ d27480 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro23933 p pair.1
    have afterEq := eqIntro19116 p pair.2
    have combined := andIntro73153 p beforeEq guard
    have complete := andIntro73471 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro19116 p pair.2
    have combined := andIntro73503 p guard beforeEq
    have complete := andIntro73547 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro19271 p pair.2
    have combined := andIntro73503 p guard beforeEq
    have complete := andIntro73591 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local923 (p : Pattern) (guard : d266246 p = 1)
    (decreasing : bonus 202 (HazardPattern.afterPattern 10000 p (.walk 202)) < bonus 223 p) :
    NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 223 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 202) + NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 202))) + bonus 202 (HazardPattern.afterPattern 10000 p (.walk 202)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 202) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) < bonus 223 p at decreasing
  rw [gammaAfter923, at223] at decreasing
  have numeric := numeric923 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202))
  rw [oldBefore223, at223, literal, oldAfter923, gammaAfter923]
  exact numeric
theorem numeric924 (p : Pattern) (guard : d236583 p = 1) (decreasing : d5849 p < d30634 p) :
    d47866 p + d30634 p ≤ (0 : Int) + d47866 p + d5849 p := by
  have beforeRange := bonus_range 223 p
  rw [at223] at beforeRange
  have afterRange := bonus_range 200 (HazardPattern.afterPattern 10000 p (.walk 200))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) ∧ bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) ≤ 2 at afterRange
  rw [gammaAfter924] at afterRange
  have possibilities : (d30634 p = 1 ∧ d5849 p = 0) ∨ (d30634 p = 2 ∧ d5849 p = 0) ∨ (d30634 p = 2 ∧ d5849 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro23933 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro73596 p guard beforeEq
    have complete := andIntro73765 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro3425 p pair.2
    have combined := andIntro73770 p guard beforeEq
    have complete := andIntro73796 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro3469 p pair.2
    have combined := andIntro73770 p guard beforeEq
    have complete := andIntro73822 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local924 (p : Pattern) (guard : d236583 p = 1)
    (decreasing : bonus 200 (HazardPattern.afterPattern 10000 p (.walk 200)) < bonus 223 p) :
    NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 223 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 200) + NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 200))) + bonus 200 (HazardPattern.afterPattern 10000 p (.walk 200)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 200) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) < bonus 223 p at decreasing
  rw [gammaAfter924, at223] at decreasing
  have numeric := numeric924 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200))
  rw [oldBefore223, at223, literal, oldAfter924, gammaAfter924]
  exact numeric
theorem numeric925 (p : Pattern) (guard : d287737 p = 1) (decreasing : d42245 p < d30634 p) :
    d47866 p + d30634 p ≤ (0 : Int) + d51138 p + d42245 p := by
  have beforeRange := bonus_range 223 p
  rw [at223] at beforeRange
  have afterRange := bonus_range 246 (HazardPattern.afterPattern 10000 p (.walk 246))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) ∧ bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) ≤ 2 at afterRange
  rw [gammaAfter925] at afterRange
  have possibilities : (d30634 p = 1 ∧ d42245 p = 0) ∨ (d30634 p = 2 ∧ d42245 p = 0) ∨ (d30634 p = 2 ∧ d42245 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro23933 p pair.1
    have afterEq := eqIntro29978 p pair.2
    have combined := andIntro74097 p beforeEq guard
    have complete := andIntro74373 p afterEq combined
    have bound := compare31961 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro29978 p pair.2
    have combined := andIntro74401 p beforeEq guard
    have complete := andIntro74444 p afterEq combined
    have bound := compare31962 p complete
    omega
  · have beforeEq := eqIntro28743 p pair.1
    have afterEq := eqIntro30116 p pair.2
    have combined := andIntro74401 p beforeEq guard
    have complete := andIntro74487 p combined afterEq
    have bound := compare31961 p complete
    omega
theorem local925 (p : Pattern) (guard : d287737 p = 1)
    (decreasing : bonus 246 (HazardPattern.afterPattern 10000 p (.walk 246)) < bonus 223 p) :
    NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 223 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 246) + NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 246))) + bonus 246 (HazardPattern.afterPattern 10000 p (.walk 246)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 246) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) < bonus 223 p at decreasing
  rw [gammaAfter925, at223] at decreasing
  have numeric := numeric925 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246))
  rw [oldBefore223, at223, literal, oldAfter925, gammaAfter925]
  exact numeric
theorem numeric926 (p : Pattern) (guard : d251389 p = 1) (decreasing : d27480 p < d33212 p) :
    d50101 p + d33212 p ≤ (0 : Int) + d47866 p + d27480 p := by
  have beforeRange := bonus_range 224 p
  rw [at224] at beforeRange
  have afterRange := bonus_range 202 (HazardPattern.afterPattern 10000 p (.walk 202))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) ∧ bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) ≤ 2 at afterRange
  rw [gammaAfter926] at afterRange
  have possibilities : (d33212 p = 1 ∧ d27480 p = 0) ∨ (d33212 p = 2 ∧ d27480 p = 0) ∨ (d33212 p = 2 ∧ d27480 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro24937 p pair.1
    have afterEq := eqIntro19116 p pair.2
    have combined := andIntro74818 p beforeEq guard
    have complete := andIntro75150 p afterEq combined
    have bound := compare31963 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro19116 p pair.2
    have combined := andIntro75182 p guard beforeEq
    have complete := andIntro75226 p afterEq combined
    have bound := compare31964 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro19271 p pair.2
    have combined := andIntro75182 p guard beforeEq
    have complete := andIntro75270 p afterEq combined
    have bound := compare31963 p complete
    omega
theorem local926 (p : Pattern) (guard : d251389 p = 1)
    (decreasing : bonus 202 (HazardPattern.afterPattern 10000 p (.walk 202)) < bonus 224 p) :
    NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 224 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 202) + NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 202))) + bonus 202 (HazardPattern.afterPattern 10000 p (.walk 202)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 202) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) < bonus 224 p at decreasing
  rw [gammaAfter926, at224] at decreasing
  have numeric := numeric926 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202))
  rw [oldBefore224, at224, literal, oldAfter926, gammaAfter926]
  exact numeric
theorem numeric927 (p : Pattern) (guard : d202307 p = 1) (decreasing : d292127 p < d33212 p) :
    d50101 p + d33212 p ≤ (2 : Int) + d47866 p + d292127 p := by
  have beforeRange := bonus_range 224 p
  rw [at224] at beforeRange
  have afterRange := bonus_range 202 (HazardPattern.afterPattern 10000 p (.push 202 (.stay 180)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 202 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 202 (.stay 180))) ∧ bonus (HazardPattern.nextHero (.push 202 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 202 (.stay 180))) ≤ 2 at afterRange
  rw [gammaAfter927] at afterRange
  have possibilities : (d33212 p = 1 ∧ d292127 p = 0) ∨ (d33212 p = 2 ∧ d292127 p = 0) ∨ (d33212 p = 2 ∧ d292127 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro24937 p pair.1
    have afterEq := eqIntro30883 p pair.2
    have combined := andIntro75601 p guard beforeEq
    have complete := andIntro75895 p afterEq combined
    have bound := compare33821 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro30883 p pair.2
    have combined := andIntro75927 p guard beforeEq
    have complete := andIntro75971 p afterEq combined
    have bound := compare34845 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro30995 p pair.2
    have combined := andIntro75927 p guard beforeEq
    have complete := andIntro76015 p combined afterEq
    have bound := compare31965 p complete
    omega
theorem local927 (p : Pattern) (guard : d202307 p = 1)
    (decreasing : bonus 202 (HazardPattern.afterPattern 10000 p (.push 202 (.stay 180))) < bonus 224 p) :
    NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 224 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 202 (.stay 180)) + NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 202 (.stay 180)))) + bonus 202 (HazardPattern.afterPattern 10000 p (.push 202 (.stay 180))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 202 (.stay 180)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 202 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 202 (.stay 180))) < bonus 224 p at decreasing
  rw [gammaAfter927, at224] at decreasing
  have numeric := numeric927 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 202 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 202 (.stay 180)))
  rw [oldBefore224, at224, literal, oldAfter927, gammaAfter927]
  exact numeric
theorem numeric928 (p : Pattern) (guard : d287735 p = 1) (decreasing : d42245 p < d33212 p) :
    d50101 p + d33212 p ≤ (0 : Int) + d51138 p + d42245 p := by
  have beforeRange := bonus_range 224 p
  rw [at224] at beforeRange
  have afterRange := bonus_range 246 (HazardPattern.afterPattern 10000 p (.walk 246))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) ∧ bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) ≤ 2 at afterRange
  rw [gammaAfter928] at afterRange
  have possibilities : (d33212 p = 1 ∧ d42245 p = 0) ∨ (d33212 p = 2 ∧ d42245 p = 0) ∨ (d33212 p = 2 ∧ d42245 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro24937 p pair.1
    have afterEq := eqIntro29978 p pair.2
    have combined := andIntro76357 p beforeEq guard
    have complete := andIntro76695 p afterEq combined
    have bound := compare34846 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro29978 p pair.2
    have combined := andIntro76727 p guard beforeEq
    have complete := andIntro76771 p afterEq combined
    have bound := compare34847 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro30116 p pair.2
    have combined := andIntro76727 p guard beforeEq
    have complete := andIntro76815 p afterEq combined
    have bound := compare34846 p complete
    omega
theorem local928 (p : Pattern) (guard : d287735 p = 1)
    (decreasing : bonus 246 (HazardPattern.afterPattern 10000 p (.walk 246)) < bonus 224 p) :
    NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 224 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 246) + NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 246))) + bonus 246 (HazardPattern.afterPattern 10000 p (.walk 246)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 246) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) < bonus 224 p at decreasing
  rw [gammaAfter928, at224] at decreasing
  have numeric := numeric928 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246))
  rw [oldBefore224, at224, literal, oldAfter928, gammaAfter928]
  exact numeric
theorem numeric929 (p : Pattern) (guard : d261985 p = 1) (decreasing : d36004 p < d33212 p) :
    d50101 p + d33212 p ≤ (0 : Int) + d50493 p + d36004 p := by
  have beforeRange := bonus_range 224 p
  rw [at224] at beforeRange
  have afterRange := bonus_range 225 (HazardPattern.afterPattern 10000 p (.walk 225))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ∧ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ≤ 2 at afterRange
  rw [gammaAfter929] at afterRange
  have possibilities : (d33212 p = 1 ∧ d36004 p = 0) ∨ (d33212 p = 2 ∧ d36004 p = 0) ∨ (d33212 p = 2 ∧ d36004 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro24937 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro77154 p beforeEq guard
    have complete := andIntro77494 p afterEq combined
    have bound := compare34848 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro77526 p guard beforeEq
    have complete := andIntro77575 p afterEq combined
    have bound := compare34849 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro26978 p pair.2
    have combined := andIntro77526 p guard beforeEq
    have complete := andIntro77619 p afterEq combined
    have bound := compare34848 p complete
    omega
theorem local929 (p : Pattern) (guard : d261985 p = 1)
    (decreasing : bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 224 p) :
    NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 224 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 225) + NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 225))) + bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 225) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 224 p at decreasing
  rw [gammaAfter929, at224] at decreasing
  have numeric := numeric929 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225))
  rw [oldBefore224, at224, literal, oldAfter929, gammaAfter929]
  exact numeric
theorem numeric930 (p : Pattern) (guard : d300100 p = 1) (decreasing : d302508 p < d33212 p) :
    d50101 p + d33212 p ≤ (0 : Int) + d300401 p + d302508 p := by
  have beforeRange := bonus_range 224 p
  rw [at224] at beforeRange
  have afterRange := bonus_range 225 (HazardPattern.afterPattern 10000 p (.push 225 (.stay 226)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 225 (.stay 226))) (HazardPattern.afterPattern 10000 p (.push 225 (.stay 226))) ∧ bonus (HazardPattern.nextHero (.push 225 (.stay 226))) (HazardPattern.afterPattern 10000 p (.push 225 (.stay 226))) ≤ 2 at afterRange
  rw [gammaAfter930] at afterRange
  have possibilities : (d33212 p = 1 ∧ d302508 p = 0) ∨ (d33212 p = 2 ∧ d302508 p = 0) ∨ (d33212 p = 2 ∧ d302508 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro24937 p pair.1
    have afterEq := eqIntro31389 p pair.2
    have combined := andIntro77995 p beforeEq guard
    have complete := andIntro78280 p afterEq combined
    have bound := compare34850 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro31389 p pair.2
    have combined := andIntro78313 p beforeEq guard
    have complete := andIntro78357 p afterEq combined
    have bound := compare34851 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro31534 p pair.2
    have combined := andIntro78313 p beforeEq guard
    have complete := andIntro78401 p combined afterEq
    have bound := compare34850 p complete
    omega
theorem local930 (p : Pattern) (guard : d300100 p = 1)
    (decreasing : bonus 225 (HazardPattern.afterPattern 10000 p (.push 225 (.stay 226))) < bonus 224 p) :
    NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 224 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 225 (.stay 226)) + NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 225 (.stay 226)))) + bonus 225 (HazardPattern.afterPattern 10000 p (.push 225 (.stay 226))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 225 (.stay 226)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 225 (.stay 226))) (HazardPattern.afterPattern 10000 p (.push 225 (.stay 226))) < bonus 224 p at decreasing
  rw [gammaAfter930, at224] at decreasing
  have numeric := numeric930 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 225 (.stay 226))) (HazardPattern.afterPattern 10000 p (.push 225 (.stay 226)))
  rw [oldBefore224, at224, literal, oldAfter930, gammaAfter930]
  exact numeric
theorem numeric931 (p : Pattern) (guard : d241830 p = 1) (decreasing : d30634 p < d33212 p) :
    d50101 p + d33212 p ≤ (0 : Int) + d47866 p + d30634 p := by
  have beforeRange := bonus_range 224 p
  rw [at224] at beforeRange
  have afterRange := bonus_range 223 (HazardPattern.afterPattern 10000 p (.walk 223))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) ∧ bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) ≤ 2 at afterRange
  rw [gammaAfter931] at afterRange
  have possibilities : (d33212 p = 1 ∧ d30634 p = 0) ∨ (d33212 p = 2 ∧ d30634 p = 0) ∨ (d33212 p = 2 ∧ d30634 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro24937 p pair.1
    have afterEq := eqIntro23817 p pair.2
    have combined := andIntro78594 p guard beforeEq
    have complete := andIntro78915 p afterEq combined
    have bound := compare31963 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro23817 p pair.2
    have combined := andIntro78935 p guard beforeEq
    have complete := andIntro78979 p afterEq combined
    have bound := compare31964 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro23933 p pair.2
    have combined := andIntro78935 p guard beforeEq
    have complete := andIntro79023 p afterEq combined
    have bound := compare31963 p complete
    omega
theorem local931 (p : Pattern) (guard : d241830 p = 1)
    (decreasing : bonus 223 (HazardPattern.afterPattern 10000 p (.walk 223)) < bonus 224 p) :
    NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 224 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 223) + NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 223))) + bonus 223 (HazardPattern.afterPattern 10000 p (.walk 223)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 223) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) < bonus 224 p at decreasing
  rw [gammaAfter931, at224] at decreasing
  have numeric := numeric931 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223))
  rw [oldBefore224, at224, literal, oldAfter931, gammaAfter931]
  exact numeric
theorem numeric932 (p : Pattern) (guard : d241832 p = 1) (decreasing : d25101 p < d33212 p) :
    d50101 p + d33212 p ≤ (0 : Int) + d47866 p + d25101 p := by
  have beforeRange := bonus_range 224 p
  rw [at224] at beforeRange
  have afterRange := bonus_range 201 (HazardPattern.afterPattern 10000 p (.walk 201))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) ∧ bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) ≤ 2 at afterRange
  rw [gammaAfter932] at afterRange
  have possibilities : (d33212 p = 1 ∧ d25101 p = 0) ∨ (d33212 p = 2 ∧ d25101 p = 0) ∨ (d33212 p = 2 ∧ d25101 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro24937 p pair.1
    have afterEq := eqIntro20211 p pair.2
    have combined := andIntro79341 p guard beforeEq
    have complete := andIntro79639 p afterEq combined
    have bound := compare31963 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro20211 p pair.2
    have combined := andIntro79671 p guard beforeEq
    have complete := andIntro79715 p afterEq combined
    have bound := compare31964 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro20354 p pair.2
    have combined := andIntro79671 p guard beforeEq
    have complete := andIntro79759 p afterEq combined
    have bound := compare31963 p complete
    omega
theorem local932 (p : Pattern) (guard : d241832 p = 1)
    (decreasing : bonus 201 (HazardPattern.afterPattern 10000 p (.walk 201)) < bonus 224 p) :
    NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 224 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 201) + NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 201))) + bonus 201 (HazardPattern.afterPattern 10000 p (.walk 201)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 201) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) < bonus 224 p at decreasing
  rw [gammaAfter932, at224] at decreasing
  have numeric := numeric932 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201))
  rw [oldBefore224, at224, literal, oldAfter932, gammaAfter932]
  exact numeric
theorem numeric933 (p : Pattern) (guard : d306035 p = 1) (decreasing : d44879 p < d33212 p) :
    d50101 p + d33212 p ≤ (0 : Int) + d51635 p + d44879 p := by
  have beforeRange := bonus_range 224 p
  rw [at224] at beforeRange
  have afterRange := bonus_range 247 (HazardPattern.afterPattern 10000 p (.walk 247))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) ∧ bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) ≤ 2 at afterRange
  rw [gammaAfter933] at afterRange
  have possibilities : (d33212 p = 1 ∧ d44879 p = 0) ∨ (d33212 p = 2 ∧ d44879 p = 0) ∨ (d33212 p = 2 ∧ d44879 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro24937 p pair.1
    have afterEq := eqIntro31994 p pair.2
    have combined := andIntro80104 p beforeEq guard
    have complete := andIntro80443 p afterEq combined
    have bound := compare34852 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro31994 p pair.2
    have combined := andIntro80475 p beforeEq guard
    have complete := andIntro80524 p afterEq combined
    have bound := compare34853 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro32161 p pair.2
    have combined := andIntro80475 p beforeEq guard
    have complete := andIntro80573 p combined afterEq
    have bound := compare34852 p complete
    omega
theorem local933 (p : Pattern) (guard : d306035 p = 1)
    (decreasing : bonus 247 (HazardPattern.afterPattern 10000 p (.walk 247)) < bonus 224 p) :
    NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 224 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 247) + NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 247))) + bonus 247 (HazardPattern.afterPattern 10000 p (.walk 247)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 247) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) < bonus 224 p at decreasing
  rw [gammaAfter933, at224] at decreasing
  have numeric := numeric933 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247))
  rw [oldBefore224, at224, literal, oldAfter933, gammaAfter933]
  exact numeric
theorem numeric934 (p : Pattern) (guard : d310057 p = 1) (decreasing : d40148 p < d33212 p) :
    d50101 p + d33212 p ≤ (0 : Int) + d47866 p + d40148 p := by
  have beforeRange := bonus_range 224 p
  rw [at224] at beforeRange
  have afterRange := bonus_range 245 (HazardPattern.afterPattern 10000 p (.walk 245))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 245)) (HazardPattern.afterPattern 10000 p (.walk 245)) ∧ bonus (HazardPattern.nextHero (.walk 245)) (HazardPattern.afterPattern 10000 p (.walk 245)) ≤ 2 at afterRange
  rw [gammaAfter934] at afterRange
  have possibilities : (d33212 p = 1 ∧ d40148 p = 0) ∨ (d33212 p = 2 ∧ d40148 p = 0) ∨ (d33212 p = 2 ∧ d40148 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro24937 p pair.1
    have afterEq := eqIntro28987 p pair.2
    have combined := andIntro80763 p beforeEq guard
    have complete := andIntro80885 p afterEq combined
    have bound := compare31963 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro28987 p pair.2
    have combined := andIntro80905 p beforeEq guard
    have complete := andIntro80925 p afterEq combined
    have bound := compare31964 p complete
    omega
  · have beforeEq := eqIntro30572 p pair.1
    have afterEq := eqIntro29076 p pair.2
    have combined := andIntro80905 p beforeEq guard
    have complete := andIntro80945 p afterEq combined
    have bound := compare31963 p complete
    omega
theorem local934 (p : Pattern) (guard : d310057 p = 1)
    (decreasing : bonus 245 (HazardPattern.afterPattern 10000 p (.walk 245)) < bonus 224 p) :
    NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 224 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 245) + NetHack.Sokoban22Refined85.bonus 245 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 245))) + bonus 245 (HazardPattern.afterPattern 10000 p (.walk 245)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 245) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 245)) (HazardPattern.afterPattern 10000 p (.walk 245)) < bonus 224 p at decreasing
  rw [gammaAfter934, at224] at decreasing
  have numeric := numeric934 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 245)) (HazardPattern.afterPattern 10000 p (.walk 245))
  rw [oldBefore224, at224, literal, oldAfter934, gammaAfter934]
  exact numeric
theorem numeric935 (p : Pattern) (guard : d310774 p = 1) (decreasing : d44879 p < d36004 p) :
    d50493 p + d36004 p ≤ (0 : Int) + d51635 p + d44879 p := by
  have beforeRange := bonus_range 225 p
  rw [at225] at beforeRange
  have afterRange := bonus_range 247 (HazardPattern.afterPattern 10000 p (.walk 247))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) ∧ bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) ≤ 2 at afterRange
  rw [gammaAfter935] at afterRange
  have possibilities : (d36004 p = 1 ∧ d44879 p = 0) ∨ (d36004 p = 2 ∧ d44879 p = 0) ∨ (d36004 p = 2 ∧ d44879 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro26978 p pair.1
    have afterEq := eqIntro31994 p pair.2
    have combined := andIntro81302 p beforeEq guard
    have complete := andIntro81587 p afterEq combined
    have bound := compare34854 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro31994 p pair.2
    have combined := andIntro81626 p guard beforeEq
    have complete := andIntro81664 p afterEq combined
    have bound := compare34855 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro32161 p pair.2
    have combined := andIntro81626 p guard beforeEq
    have complete := andIntro81702 p afterEq combined
    have bound := compare34854 p complete
    omega
theorem local935 (p : Pattern) (guard : d310774 p = 1)
    (decreasing : bonus 247 (HazardPattern.afterPattern 10000 p (.walk 247)) < bonus 225 p) :
    NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 225 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 247) + NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 247))) + bonus 247 (HazardPattern.afterPattern 10000 p (.walk 247)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 247) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) < bonus 225 p at decreasing
  rw [gammaAfter935, at225] at decreasing
  have numeric := numeric935 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247))
  rw [oldBefore225, at225, literal, oldAfter935, gammaAfter935]
  exact numeric
theorem numeric936 (p : Pattern) (guard : d277739 p = 1) (decreasing : d38812 p < d36004 p) :
    d50493 p + d36004 p ≤ (0 : Int) + d50823 p + d38812 p := by
  have beforeRange := bonus_range 225 p
  rw [at225] at beforeRange
  have afterRange := bonus_range 226 (HazardPattern.afterPattern 10000 p (.walk 226))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) ∧ bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) ≤ 2 at afterRange
  rw [gammaAfter936] at afterRange
  have possibilities : (d36004 p = 1 ∧ d38812 p = 0) ∨ (d36004 p = 2 ∧ d38812 p = 0) ∨ (d36004 p = 2 ∧ d38812 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro26978 p pair.1
    have afterEq := eqIntro27657 p pair.2
    have combined := andIntro82056 p beforeEq guard
    have complete := andIntro82409 p afterEq combined
    have bound := compare34856 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro27657 p pair.2
    have combined := andIntro82447 p guard beforeEq
    have complete := andIntro82500 p afterEq combined
    have bound := compare34857 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro27833 p pair.2
    have combined := andIntro82447 p guard beforeEq
    have complete := andIntro82544 p afterEq combined
    have bound := compare34856 p complete
    omega
theorem local936 (p : Pattern) (guard : d277739 p = 1)
    (decreasing : bonus 226 (HazardPattern.afterPattern 10000 p (.walk 226)) < bonus 225 p) :
    NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 225 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 226) + NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 226))) + bonus 226 (HazardPattern.afterPattern 10000 p (.walk 226)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 226) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) < bonus 225 p at decreasing
  rw [gammaAfter936, at225] at decreasing
  have numeric := numeric936 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226))
  rw [oldBefore225, at225, literal, oldAfter936, gammaAfter936]
  exact numeric
theorem numeric937 (p : Pattern) (guard : d261985 p = 1) (decreasing : d33212 p < d36004 p) :
    d50493 p + d36004 p ≤ (0 : Int) + d50101 p + d33212 p := by
  have beforeRange := bonus_range 225 p
  rw [at225] at beforeRange
  have afterRange := bonus_range 224 (HazardPattern.afterPattern 10000 p (.walk 224))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ∧ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ≤ 2 at afterRange
  rw [gammaAfter937] at afterRange
  have possibilities : (d36004 p = 1 ∧ d33212 p = 0) ∨ (d36004 p = 2 ∧ d33212 p = 0) ∨ (d36004 p = 2 ∧ d33212 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro26978 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro82894 p guard beforeEq
    have complete := andIntro83231 p afterEq combined
    have bound := compare34858 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro83270 p guard beforeEq
    have complete := andIntro83314 p afterEq combined
    have bound := compare34859 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro24937 p pair.2
    have combined := andIntro83270 p guard beforeEq
    have complete := andIntro83358 p afterEq combined
    have bound := compare34858 p complete
    omega
theorem local937 (p : Pattern) (guard : d261985 p = 1)
    (decreasing : bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 225 p) :
    NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 225 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 224) + NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 224))) + bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 224) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 225 p at decreasing
  rw [gammaAfter937, at225] at decreasing
  have numeric := numeric937 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224))
  rw [oldBefore225, at225, literal, oldAfter937, gammaAfter937]
  exact numeric
theorem numeric938 (p : Pattern) (guard : d282284 p = 1) (decreasing : d315158 p < d36004 p) :
    d50493 p + d36004 p ≤ (4 : Int) + d47866 p + d315158 p := by
  have beforeRange := bonus_range 225 p
  rw [at225] at beforeRange
  have afterRange := bonus_range 224 (HazardPattern.afterPattern 10000 p (.push 224 (.stay 223)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 224 (.stay 223))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 223))) ∧ bonus (HazardPattern.nextHero (.push 224 (.stay 223))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 223))) ≤ 2 at afterRange
  rw [gammaAfter938] at afterRange
  have possibilities : (d36004 p = 1 ∧ d315158 p = 0) ∨ (d36004 p = 2 ∧ d315158 p = 0) ∨ (d36004 p = 2 ∧ d315158 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro26978 p pair.1
    have afterEq := eqIntro32903 p pair.2
    have combined := andIntro83711 p beforeEq guard
    have complete := andIntro83893 p afterEq combined
    have bound := compare37815 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro32903 p pair.2
    have combined := andIntro83931 p guard beforeEq
    have complete := andIntro83964 p afterEq combined
    have bound := compare39610 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro32996 p pair.2
    have combined := andIntro83931 p guard beforeEq
    have complete := andIntro83990 p combined afterEq
    have bound := compare34860 p complete
    omega
theorem local938 (p : Pattern) (guard : d282284 p = 1)
    (decreasing : bonus 224 (HazardPattern.afterPattern 10000 p (.push 224 (.stay 223))) < bonus 225 p) :
    NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 225 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 224 (.stay 223)) + NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 224 (.stay 223)))) + bonus 224 (HazardPattern.afterPattern 10000 p (.push 224 (.stay 223))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 224 (.stay 223)) = (4 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 224 (.stay 223))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 223))) < bonus 225 p at decreasing
  rw [gammaAfter938, at225] at decreasing
  have numeric := numeric938 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 224 (.stay 223))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 223)))
  rw [oldBefore225, at225, literal, oldAfter938, gammaAfter938]
  exact numeric
theorem numeric939 (p : Pattern) (guard : d277740 p = 1) (decreasing : d28738 p < d36004 p) :
    d50493 p + d36004 p ≤ (0 : Int) + d49782 p + d28738 p := by
  have beforeRange := bonus_range 225 p
  rw [at225] at beforeRange
  have afterRange := bonus_range 204 (HazardPattern.afterPattern 10000 p (.walk 204))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) ∧ bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) ≤ 2 at afterRange
  rw [gammaAfter939] at afterRange
  have possibilities : (d36004 p = 1 ∧ d28738 p = 0) ∨ (d36004 p = 2 ∧ d28738 p = 0) ∨ (d36004 p = 2 ∧ d28738 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro26978 p pair.1
    have afterEq := eqIntro20553 p pair.2
    have combined := andIntro84329 p beforeEq guard
    have complete := andIntro84682 p afterEq combined
    have bound := compare39611 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro20553 p pair.2
    have combined := andIntro84720 p guard beforeEq
    have complete := andIntro84770 p afterEq combined
    have bound := compare39612 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro20627 p pair.2
    have combined := andIntro84720 p guard beforeEq
    have complete := andIntro84814 p afterEq combined
    have bound := compare39611 p complete
    omega
theorem local939 (p : Pattern) (guard : d277740 p = 1)
    (decreasing : bonus 204 (HazardPattern.afterPattern 10000 p (.walk 204)) < bonus 225 p) :
    NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 225 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 204) + NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 204))) + bonus 204 (HazardPattern.afterPattern 10000 p (.walk 204)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 204) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) < bonus 225 p at decreasing
  rw [gammaAfter939, at225] at decreasing
  have numeric := numeric939 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204))
  rw [oldBefore225, at225, literal, oldAfter939, gammaAfter939]
  exact numeric
theorem numeric940 (p : Pattern) (guard : d261986 p = 1) (decreasing : d27480 p < d36004 p) :
    d50493 p + d36004 p ≤ (0 : Int) + d47866 p + d27480 p := by
  have beforeRange := bonus_range 225 p
  rw [at225] at beforeRange
  have afterRange := bonus_range 202 (HazardPattern.afterPattern 10000 p (.walk 202))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) ∧ bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) ≤ 2 at afterRange
  rw [gammaAfter940] at afterRange
  have possibilities : (d36004 p = 1 ∧ d27480 p = 0) ∨ (d36004 p = 2 ∧ d27480 p = 0) ∨ (d36004 p = 2 ∧ d27480 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro26978 p pair.1
    have afterEq := eqIntro19116 p pair.2
    have combined := andIntro85153 p guard beforeEq
    have complete := andIntro85481 p afterEq combined
    have bound := compare39613 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro19116 p pair.2
    have combined := andIntro85519 p guard beforeEq
    have complete := andIntro85563 p afterEq combined
    have bound := compare39614 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro19271 p pair.2
    have combined := andIntro85519 p guard beforeEq
    have complete := andIntro85607 p afterEq combined
    have bound := compare39613 p complete
    omega
theorem local940 (p : Pattern) (guard : d261986 p = 1)
    (decreasing : bonus 202 (HazardPattern.afterPattern 10000 p (.walk 202)) < bonus 225 p) :
    NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 225 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 202) + NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 202))) + bonus 202 (HazardPattern.afterPattern 10000 p (.walk 202)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 202) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) < bonus 225 p at decreasing
  rw [gammaAfter940, at225] at decreasing
  have numeric := numeric940 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202))
  rw [oldBefore225, at225, literal, oldAfter940, gammaAfter940]
  exact numeric
theorem numeric941 (p : Pattern) (guard : d318725 p = 1) (decreasing : d47282 p < d36004 p) :
    d50493 p + d36004 p ≤ (0 : Int) + d50823 p + d47282 p := by
  have beforeRange := bonus_range 225 p
  rw [at225] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.walk 248))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248)) ∧ bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248)) ≤ 2 at afterRange
  rw [gammaAfter941] at afterRange
  have possibilities : (d36004 p = 1 ∧ d47282 p = 0) ∨ (d36004 p = 2 ∧ d47282 p = 0) ∨ (d36004 p = 2 ∧ d47282 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro26978 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro85973 p beforeEq guard
    have complete := andIntro86292 p afterEq combined
    have bound := compare34856 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro86330 p beforeEq guard
    have complete := andIntro86383 p afterEq combined
    have bound := compare34857 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro33595 p pair.2
    have combined := andIntro86330 p beforeEq guard
    have complete := andIntro86432 p combined afterEq
    have bound := compare34856 p complete
    omega
theorem local941 (p : Pattern) (guard : d318725 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.walk 248)) < bonus 225 p) :
    NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 225 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 248) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 248))) + bonus 248 (HazardPattern.afterPattern 10000 p (.walk 248)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 248) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248)) < bonus 225 p at decreasing
  rw [gammaAfter941, at225] at decreasing
  have numeric := numeric941 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248))
  rw [oldBefore225, at225, literal, oldAfter941, gammaAfter941]
  exact numeric
theorem numeric942 (p : Pattern) (guard : d322255 p = 1) (decreasing : d42245 p < d36004 p) :
    d50493 p + d36004 p ≤ (0 : Int) + d51138 p + d42245 p := by
  have beforeRange := bonus_range 225 p
  rw [at225] at beforeRange
  have afterRange := bonus_range 246 (HazardPattern.afterPattern 10000 p (.walk 246))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) ∧ bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) ≤ 2 at afterRange
  rw [gammaAfter942] at afterRange
  have possibilities : (d36004 p = 1 ∧ d42245 p = 0) ∨ (d36004 p = 2 ∧ d42245 p = 0) ∨ (d36004 p = 2 ∧ d42245 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro26978 p pair.1
    have afterEq := eqIntro29978 p pair.2
    have combined := andIntro86793 p beforeEq guard
    have complete := andIntro87129 p afterEq combined
    have bound := compare39615 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro29978 p pair.2
    have combined := andIntro87168 p beforeEq guard
    have complete := andIntro87212 p afterEq combined
    have bound := compare39616 p complete
    omega
  · have beforeEq := eqIntro32645 p pair.1
    have afterEq := eqIntro30116 p pair.2
    have combined := andIntro87168 p beforeEq guard
    have complete := andIntro87256 p afterEq combined
    have bound := compare39615 p complete
    omega
theorem local942 (p : Pattern) (guard : d322255 p = 1)
    (decreasing : bonus 246 (HazardPattern.afterPattern 10000 p (.walk 246)) < bonus 225 p) :
    NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 225 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 246) + NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 246))) + bonus 246 (HazardPattern.afterPattern 10000 p (.walk 246)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 246) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) < bonus 225 p at decreasing
  rw [gammaAfter942, at225] at decreasing
  have numeric := numeric942 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246))
  rw [oldBefore225, at225, literal, oldAfter942, gammaAfter942]
  exact numeric
theorem numeric943 (p : Pattern) (guard : d267844 p = 1) (decreasing : d28738 p < d38812 p) :
    d50823 p + d38812 p ≤ (0 : Int) + d49782 p + d28738 p := by
  have beforeRange := bonus_range 226 p
  rw [at226] at beforeRange
  have afterRange := bonus_range 204 (HazardPattern.afterPattern 10000 p (.walk 204))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) ∧ bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) ≤ 2 at afterRange
  rw [gammaAfter943] at afterRange
  have possibilities : (d38812 p = 1 ∧ d28738 p = 0) ∨ (d38812 p = 2 ∧ d28738 p = 0) ∨ (d38812 p = 2 ∧ d28738 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro27833 p pair.1
    have afterEq := eqIntro20553 p pair.2
    have combined := andIntro87401 p guard beforeEq
    have complete := andIntro87754 p afterEq combined
    have bound := compare39617 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro20553 p pair.2
    have combined := andIntro87778 p guard beforeEq
    have complete := andIntro87828 p afterEq combined
    have bound := compare39618 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro20627 p pair.2
    have combined := andIntro87778 p guard beforeEq
    have complete := andIntro87872 p afterEq combined
    have bound := compare39617 p complete
    omega
theorem local943 (p : Pattern) (guard : d267844 p = 1)
    (decreasing : bonus 204 (HazardPattern.afterPattern 10000 p (.walk 204)) < bonus 226 p) :
    NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 226 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 204) + NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 204))) + bonus 204 (HazardPattern.afterPattern 10000 p (.walk 204)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 204) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) < bonus 226 p at decreasing
  rw [gammaAfter943, at226] at decreasing
  have numeric := numeric943 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204))
  rw [oldBefore226, at226, literal, oldAfter943, gammaAfter943]
  exact numeric
theorem numeric944 (p : Pattern) (guard : d216471 p = 1) (decreasing : d0 p < d38812 p) :
    d50823 p + d38812 p ≤ (2 : Int) + d324611 p + d0 p := by
  have beforeRange := bonus_range 226 p
  rw [at226] at beforeRange
  have afterRange := bonus_range 204 (HazardPattern.afterPattern 10000 p (.push 204 (.stay 182)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 204 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 204 (.stay 182))) ∧ bonus (HazardPattern.nextHero (.push 204 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 204 (.stay 182))) ≤ 2 at afterRange
  rw [gammaAfter944] at afterRange
  have possibilities : (d38812 p = 1 ∧ d0 p = 0) ∨ (d38812 p = 2 ∧ d0 p = 0) ∨ (d38812 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro27833 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro88215 p guard beforeEq
    have complete := andIntro88216 p afterEq combined
    have bound := compare40587 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro88256 p guard beforeEq
    have complete := andIntro88257 p afterEq combined
    have bound := compare41206 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro88256 p guard beforeEq
    have complete := andIntro88258 p afterEq combined
    have bound := compare39619 p complete
    omega
theorem local944 (p : Pattern) (guard : d216471 p = 1)
    (decreasing : bonus 204 (HazardPattern.afterPattern 10000 p (.push 204 (.stay 182))) < bonus 226 p) :
    NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 226 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 204 (.stay 182)) + NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 204 (.stay 182)))) + bonus 204 (HazardPattern.afterPattern 10000 p (.push 204 (.stay 182))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 204 (.stay 182)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 204 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 204 (.stay 182))) < bonus 226 p at decreasing
  rw [gammaAfter944, at226] at decreasing
  have numeric := numeric944 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 204 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 204 (.stay 182)))
  rw [oldBefore226, at226, literal, oldAfter944, gammaAfter944]
  exact numeric
theorem numeric945 (p : Pattern) (guard : d325306 p = 1) (decreasing : d47282 p < d38812 p) :
    d50823 p + d38812 p ≤ (0 : Int) + d50823 p + d47282 p := by
  have beforeRange := bonus_range 226 p
  rw [at226] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.walk 248))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248)) ∧ bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248)) ≤ 2 at afterRange
  rw [gammaAfter945] at afterRange
  have possibilities : (d38812 p = 1 ∧ d47282 p = 0) ∨ (d38812 p = 2 ∧ d47282 p = 0) ∨ (d38812 p = 2 ∧ d47282 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro27833 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro88621 p beforeEq guard
    have complete := andIntro88889 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro88929 p beforeEq guard
    have complete := andIntro88975 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro33595 p pair.2
    have combined := andIntro88929 p beforeEq guard
    have complete := andIntro89016 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local945 (p : Pattern) (guard : d325306 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.walk 248)) < bonus 226 p) :
    NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 226 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 248) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 248))) + bonus 248 (HazardPattern.afterPattern 10000 p (.walk 248)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 248) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248)) < bonus 226 p at decreasing
  rw [gammaAfter945, at226] at decreasing
  have numeric := numeric945 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248))
  rw [oldBefore226, at226, literal, oldAfter945, gammaAfter945]
  exact numeric
theorem numeric946 (p : Pattern) (guard : d277739 p = 1) (decreasing : d36004 p < d38812 p) :
    d50823 p + d38812 p ≤ (0 : Int) + d50493 p + d36004 p := by
  have beforeRange := bonus_range 226 p
  rw [at226] at beforeRange
  have afterRange := bonus_range 225 (HazardPattern.afterPattern 10000 p (.walk 225))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ∧ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ≤ 2 at afterRange
  rw [gammaAfter946] at afterRange
  have possibilities : (d38812 p = 1 ∧ d36004 p = 0) ∨ (d38812 p = 2 ∧ d36004 p = 0) ∨ (d38812 p = 2 ∧ d36004 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro27833 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro89364 p beforeEq guard
    have complete := andIntro89503 p afterEq combined
    have bound := compare41209 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro89544 p guard beforeEq
    have complete := andIntro89571 p afterEq combined
    have bound := compare41210 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro26978 p pair.2
    have combined := andIntro89544 p guard beforeEq
    have complete := andIntro89591 p afterEq combined
    have bound := compare41209 p complete
    omega
theorem local946 (p : Pattern) (guard : d277739 p = 1)
    (decreasing : bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 226 p) :
    NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 226 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 225) + NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 225))) + bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 225) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 226 p at decreasing
  rw [gammaAfter946, at226] at decreasing
  have numeric := numeric946 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225))
  rw [oldBefore226, at226, literal, oldAfter946, gammaAfter946]
  exact numeric
theorem numeric947 (p : Pattern) (guard : d300100 p = 1) (decreasing : d328724 p < d38812 p) :
    d50823 p + d38812 p ≤ (2 : Int) + d326947 p + d328724 p := by
  have beforeRange := bonus_range 226 p
  rw [at226] at beforeRange
  have afterRange := bonus_range 225 (HazardPattern.afterPattern 10000 p (.push 225 (.stay 224)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 225 (.stay 224))) (HazardPattern.afterPattern 10000 p (.push 225 (.stay 224))) ∧ bonus (HazardPattern.nextHero (.push 225 (.stay 224))) (HazardPattern.afterPattern 10000 p (.push 225 (.stay 224))) ≤ 2 at afterRange
  rw [gammaAfter947] at afterRange
  have possibilities : (d38812 p = 1 ∧ d328724 p = 0) ∨ (d38812 p = 2 ∧ d328724 p = 0) ∨ (d38812 p = 2 ∧ d328724 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro27833 p pair.1
    have afterEq := eqIntro34384 p pair.2
    have combined := andIntro89952 p beforeEq guard
    have complete := andIntro90237 p afterEq combined
    have bound := compare41211 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro34384 p pair.2
    have combined := andIntro90278 p guard beforeEq
    have complete := andIntro90329 p afterEq combined
    have bound := compare41212 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro34504 p pair.2
    have combined := andIntro90278 p guard beforeEq
    have complete := andIntro90373 p combined afterEq
    have bound := compare41211 p complete
    omega
theorem local947 (p : Pattern) (guard : d300100 p = 1)
    (decreasing : bonus 225 (HazardPattern.afterPattern 10000 p (.push 225 (.stay 224))) < bonus 226 p) :
    NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 226 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 225 (.stay 224)) + NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 225 (.stay 224)))) + bonus 225 (HazardPattern.afterPattern 10000 p (.push 225 (.stay 224))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 225 (.stay 224)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 225 (.stay 224))) (HazardPattern.afterPattern 10000 p (.push 225 (.stay 224))) < bonus 226 p at decreasing
  rw [gammaAfter947, at226] at decreasing
  have numeric := numeric947 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 225 (.stay 224))) (HazardPattern.afterPattern 10000 p (.push 225 (.stay 224)))
  rw [oldBefore226, at226, literal, oldAfter947, gammaAfter947]
  exact numeric
theorem numeric948 (p : Pattern) (guard : d331330 p = 1) (decreasing : d47282 p < d38812 p) :
    d50823 p + d38812 p ≤ (0 : Int) + d50823 p + d47282 p := by
  have beforeRange := bonus_range 226 p
  rw [at226] at beforeRange
  have afterRange := bonus_range 249 (HazardPattern.afterPattern 10000 p (.walk 249))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 249)) (HazardPattern.afterPattern 10000 p (.walk 249)) ∧ bonus (HazardPattern.nextHero (.walk 249)) (HazardPattern.afterPattern 10000 p (.walk 249)) ≤ 2 at afterRange
  rw [gammaAfter948] at afterRange
  have possibilities : (d38812 p = 1 ∧ d47282 p = 0) ∨ (d38812 p = 2 ∧ d47282 p = 0) ∨ (d38812 p = 2 ∧ d47282 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro27833 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro90379 p beforeEq guard
    have complete := andIntro88889 p afterEq combined
    have bound := compare41207 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro90385 p beforeEq guard
    have complete := andIntro88975 p afterEq combined
    have bound := compare41208 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro33595 p pair.2
    have combined := andIntro90385 p beforeEq guard
    have complete := andIntro89016 p afterEq combined
    have bound := compare41207 p complete
    omega
theorem local948 (p : Pattern) (guard : d331330 p = 1)
    (decreasing : bonus 249 (HazardPattern.afterPattern 10000 p (.walk 249)) < bonus 226 p) :
    NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 226 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 249) + NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 249))) + bonus 249 (HazardPattern.afterPattern 10000 p (.walk 249)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 249) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 249)) (HazardPattern.afterPattern 10000 p (.walk 249)) < bonus 226 p at decreasing
  rw [gammaAfter948, at226] at decreasing
  have numeric := numeric948 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 249)) (HazardPattern.afterPattern 10000 p (.walk 249))
  rw [oldBefore226, at226, literal, oldAfter948, gammaAfter948]
  exact numeric
theorem numeric949 (p : Pattern) (guard : d331335 p = 1) (decreasing : d44879 p < d38812 p) :
    d50823 p + d38812 p ≤ (0 : Int) + d51635 p + d44879 p := by
  have beforeRange := bonus_range 226 p
  rw [at226] at beforeRange
  have afterRange := bonus_range 247 (HazardPattern.afterPattern 10000 p (.walk 247))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) ∧ bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) ≤ 2 at afterRange
  rw [gammaAfter949] at afterRange
  have possibilities : (d38812 p = 1 ∧ d44879 p = 0) ∨ (d38812 p = 2 ∧ d44879 p = 0) ∨ (d38812 p = 2 ∧ d44879 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro27833 p pair.1
    have afterEq := eqIntro31994 p pair.2
    have combined := andIntro90740 p beforeEq guard
    have complete := andIntro91076 p afterEq combined
    have bound := compare41213 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro31994 p pair.2
    have combined := andIntro91117 p beforeEq guard
    have complete := andIntro91161 p afterEq combined
    have bound := compare41214 p complete
    omega
  · have beforeEq := eqIntro34075 p pair.1
    have afterEq := eqIntro32161 p pair.2
    have combined := andIntro91117 p beforeEq guard
    have complete := andIntro91205 p afterEq combined
    have bound := compare41213 p complete
    omega
theorem local949 (p : Pattern) (guard : d331335 p = 1)
    (decreasing : bonus 247 (HazardPattern.afterPattern 10000 p (.walk 247)) < bonus 226 p) :
    NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 226 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 247) + NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 247))) + bonus 247 (HazardPattern.afterPattern 10000 p (.walk 247)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 247) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) < bonus 226 p at decreasing
  rw [gammaAfter949, at226] at decreasing
  have numeric := numeric949 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247))
  rw [oldBefore226, at226, literal, oldAfter949, gammaAfter949]
  exact numeric
theorem numeric950 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 240 p
  rw [at240] at beforeRange
  have afterRange := bonus_range 218 (HazardPattern.afterPattern 10000 p (.walk 218))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 218)) (HazardPattern.afterPattern 10000 p (.walk 218)) ∧ bonus (HazardPattern.nextHero (.walk 218)) (HazardPattern.afterPattern 10000 p (.walk 218)) ≤ 2 at afterRange
  rw [gammaAfter950] at afterRange
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
theorem local950 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 218 (HazardPattern.afterPattern 10000 p (.walk 218)) < bonus 240 p) :
    NetHack.Sokoban22Refined85.bonus 240 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 240 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 218) + NetHack.Sokoban22Refined85.bonus 218 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 218))) + bonus 218 (HazardPattern.afterPattern 10000 p (.walk 218)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 218) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 218)) (HazardPattern.afterPattern 10000 p (.walk 218)) < bonus 240 p at decreasing
  rw [gammaAfter950, at240] at decreasing
  have numeric := numeric950 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 218)) (HazardPattern.afterPattern 10000 p (.walk 218))
  rw [oldBefore240, at240, literal, oldAfter950, gammaAfter950]
  exact numeric
theorem numeric951 (p : Pattern) (guard : d1 p = 1) (decreasing : d0 p < d0 p) :
    d0 p + d0 p ≤ (0 : Int) + d0 p + d0 p := by
  have beforeRange := bonus_range 240 p
  rw [at240] at beforeRange
  have afterRange := bonus_range 262 (HazardPattern.afterPattern 10000 p (.walk 262))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 262)) (HazardPattern.afterPattern 10000 p (.walk 262)) ∧ bonus (HazardPattern.nextHero (.walk 262)) (HazardPattern.afterPattern 10000 p (.walk 262)) ≤ 2 at afterRange
  rw [gammaAfter951] at afterRange
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
theorem local951 (p : Pattern) (guard : d1 p = 1)
    (decreasing : bonus 262 (HazardPattern.afterPattern 10000 p (.walk 262)) < bonus 240 p) :
    NetHack.Sokoban22Refined85.bonus 240 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 240 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 262) + NetHack.Sokoban22Refined85.bonus 262 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 262))) + bonus 262 (HazardPattern.afterPattern 10000 p (.walk 262)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 262) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 262)) (HazardPattern.afterPattern 10000 p (.walk 262)) < bonus 240 p at decreasing
  rw [gammaAfter951, at240] at decreasing
  have numeric := numeric951 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 262)) (HazardPattern.afterPattern 10000 p (.walk 262))
  rw [oldBefore240, at240, literal, oldAfter951, gammaAfter951]
  exact numeric
theorem numeric952 (p : Pattern) (guard : d279951 p = 1) (decreasing : d30634 p < d40148 p) :
    d47866 p + d40148 p ≤ (0 : Int) + d47866 p + d30634 p := by
  have beforeRange := bonus_range 245 p
  rw [at245] at beforeRange
  have afterRange := bonus_range 223 (HazardPattern.afterPattern 10000 p (.walk 223))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) ∧ bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) ≤ 2 at afterRange
  rw [gammaAfter952] at afterRange
  have possibilities : (d40148 p = 1 ∧ d30634 p = 0) ∨ (d40148 p = 2 ∧ d30634 p = 0) ∨ (d40148 p = 2 ∧ d30634 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro29076 p pair.1
    have afterEq := eqIntro23817 p pair.2
    have combined := andIntro91387 p guard beforeEq
    have complete := andIntro91563 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro34748 p pair.1
    have afterEq := eqIntro23817 p pair.2
    have combined := andIntro91583 p guard beforeEq
    have complete := andIntro91609 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro34748 p pair.1
    have afterEq := eqIntro23933 p pair.2
    have combined := andIntro91583 p guard beforeEq
    have complete := andIntro91635 p afterEq combined
    have bound := compare0 p complete
    omega
theorem local952 (p : Pattern) (guard : d279951 p = 1)
    (decreasing : bonus 223 (HazardPattern.afterPattern 10000 p (.walk 223)) < bonus 245 p) :
    NetHack.Sokoban22Refined85.bonus 245 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 245 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 223) + NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 223))) + bonus 223 (HazardPattern.afterPattern 10000 p (.walk 223)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 223) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) < bonus 245 p at decreasing
  rw [gammaAfter952, at245] at decreasing
  have numeric := numeric952 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223))
  rw [oldBefore245, at245, literal, oldAfter952, gammaAfter952]
  exact numeric
theorem numeric953 (p : Pattern) (guard : d239127 p = 1) (decreasing : d335575 p < d40148 p) :
    d47866 p + d40148 p ≤ (0 : Int) + d47866 p + d335575 p := by
  have beforeRange := bonus_range 245 p
  rw [at245] at beforeRange
  have afterRange := bonus_range 223 (HazardPattern.afterPattern 10000 p (.push 223 (.stay 201)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 223 (.stay 201))) (HazardPattern.afterPattern 10000 p (.push 223 (.stay 201))) ∧ bonus (HazardPattern.nextHero (.push 223 (.stay 201))) (HazardPattern.afterPattern 10000 p (.push 223 (.stay 201))) ≤ 2 at afterRange
  rw [gammaAfter953] at afterRange
  have possibilities : (d40148 p = 1 ∧ d335575 p = 0) ∨ (d40148 p = 2 ∧ d335575 p = 0) ∨ (d40148 p = 2 ∧ d335575 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro29076 p pair.1
    have afterEq := eqIntro35131 p pair.2
    have combined := andIntro91961 p guard beforeEq
    have complete := andIntro92145 p afterEq combined
    have bound := compare0 p complete
    omega
  · have beforeEq := eqIntro34748 p pair.1
    have afterEq := eqIntro35131 p pair.2
    have combined := andIntro92177 p guard beforeEq
    have complete := andIntro92203 p afterEq combined
    have bound := compare1 p complete
    omega
  · have beforeEq := eqIntro34748 p pair.1
    have afterEq := eqIntro35268 p pair.2
    have combined := andIntro92177 p guard beforeEq
    have complete := andIntro92229 p combined afterEq
    have bound := compare0 p complete
    omega
theorem local953 (p : Pattern) (guard : d239127 p = 1)
    (decreasing : bonus 223 (HazardPattern.afterPattern 10000 p (.push 223 (.stay 201))) < bonus 245 p) :
    NetHack.Sokoban22Refined85.bonus 245 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 245 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 223 (.stay 201)) + NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 223 (.stay 201)))) + bonus 223 (HazardPattern.afterPattern 10000 p (.push 223 (.stay 201))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 223 (.stay 201)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 223 (.stay 201))) (HazardPattern.afterPattern 10000 p (.push 223 (.stay 201))) < bonus 245 p at decreasing
  rw [gammaAfter953, at245] at decreasing
  have numeric := numeric953 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 223 (.stay 201))) (HazardPattern.afterPattern 10000 p (.push 223 (.stay 201)))
  rw [oldBefore245, at245, literal, oldAfter953, gammaAfter953]
  exact numeric
theorem numeric954 (p : Pattern) (guard : d338547 p = 1) (decreasing : d42245 p < d40148 p) :
    d47866 p + d40148 p ≤ (0 : Int) + d51138 p + d42245 p := by
  have beforeRange := bonus_range 245 p
  rw [at245] at beforeRange
  have afterRange := bonus_range 246 (HazardPattern.afterPattern 10000 p (.walk 246))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) ∧ bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) ≤ 2 at afterRange
  rw [gammaAfter954] at afterRange
  have possibilities : (d40148 p = 1 ∧ d42245 p = 0) ∨ (d40148 p = 2 ∧ d42245 p = 0) ∨ (d40148 p = 2 ∧ d42245 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro29076 p pair.1
    have afterEq := eqIntro29978 p pair.2
    have combined := andIntro92496 p beforeEq guard
    have complete := andIntro92675 p afterEq combined
    have bound := compare31961 p complete
    omega
  · have beforeEq := eqIntro34748 p pair.1
    have afterEq := eqIntro29978 p pair.2
    have combined := andIntro92703 p beforeEq guard
    have complete := andIntro92729 p afterEq combined
    have bound := compare31962 p complete
    omega
  · have beforeEq := eqIntro34748 p pair.1
    have afterEq := eqIntro30116 p pair.2
    have combined := andIntro92703 p beforeEq guard
    have complete := andIntro92755 p afterEq combined
    have bound := compare31961 p complete
    omega
theorem local954 (p : Pattern) (guard : d338547 p = 1)
    (decreasing : bonus 246 (HazardPattern.afterPattern 10000 p (.walk 246)) < bonus 245 p) :
    NetHack.Sokoban22Refined85.bonus 245 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 245 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 246) + NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 246))) + bonus 246 (HazardPattern.afterPattern 10000 p (.walk 246)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 246) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) < bonus 245 p at decreasing
  rw [gammaAfter954, at245] at decreasing
  have numeric := numeric954 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246))
  rw [oldBefore245, at245, literal, oldAfter954, gammaAfter954]
  exact numeric
theorem numeric955 (p : Pattern) (guard : d338652 p = 1) (decreasing : d341089 p < d40148 p) :
    d47866 p + d40148 p ≤ (0 : Int) + d338883 p + d341089 p := by
  have beforeRange := bonus_range 245 p
  rw [at245] at beforeRange
  have afterRange := bonus_range 246 (HazardPattern.afterPattern 10000 p (.push 246 (.stay 247)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 246 (.stay 247))) (HazardPattern.afterPattern 10000 p (.push 246 (.stay 247))) ∧ bonus (HazardPattern.nextHero (.push 246 (.stay 247))) (HazardPattern.afterPattern 10000 p (.push 246 (.stay 247))) ≤ 2 at afterRange
  rw [gammaAfter955] at afterRange
  have possibilities : (d40148 p = 1 ∧ d341089 p = 0) ∨ (d40148 p = 2 ∧ d341089 p = 0) ∨ (d40148 p = 2 ∧ d341089 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro29076 p pair.1
    have afterEq := eqIntro35665 p pair.2
    have combined := andIntro93131 p beforeEq guard
    have complete := andIntro93362 p afterEq combined
    have bound := compare41215 p complete
    omega
  · have beforeEq := eqIntro34748 p pair.1
    have afterEq := eqIntro35665 p pair.2
    have combined := andIntro93395 p beforeEq guard
    have complete := andIntro93433 p afterEq combined
    have bound := compare41216 p complete
    omega
  · have beforeEq := eqIntro34748 p pair.1
    have afterEq := eqIntro35813 p pair.2
    have combined := andIntro93395 p beforeEq guard
    have complete := andIntro93471 p combined afterEq
    have bound := compare41215 p complete
    omega
theorem local955 (p : Pattern) (guard : d338652 p = 1)
    (decreasing : bonus 246 (HazardPattern.afterPattern 10000 p (.push 246 (.stay 247))) < bonus 245 p) :
    NetHack.Sokoban22Refined85.bonus 245 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 245 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 246 (.stay 247)) + NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 246 (.stay 247)))) + bonus 246 (HazardPattern.afterPattern 10000 p (.push 246 (.stay 247))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 246 (.stay 247)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 246 (.stay 247))) (HazardPattern.afterPattern 10000 p (.push 246 (.stay 247))) < bonus 245 p at decreasing
  rw [gammaAfter955, at245] at decreasing
  have numeric := numeric955 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 246 (.stay 247))) (HazardPattern.afterPattern 10000 p (.push 246 (.stay 247)))
  rw [oldBefore245, at245, literal, oldAfter955, gammaAfter955]
  exact numeric
theorem numeric956 (p : Pattern) (guard : d310057 p = 1) (decreasing : d33212 p < d40148 p) :
    d47866 p + d40148 p ≤ (0 : Int) + d50101 p + d33212 p := by
  have beforeRange := bonus_range 245 p
  rw [at245] at beforeRange
  have afterRange := bonus_range 224 (HazardPattern.afterPattern 10000 p (.walk 224))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ∧ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ≤ 2 at afterRange
  rw [gammaAfter956] at afterRange
  have possibilities : (d40148 p = 1 ∧ d33212 p = 0) ∨ (d40148 p = 2 ∧ d33212 p = 0) ∨ (d40148 p = 2 ∧ d33212 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro29076 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro93802 p beforeEq guard
    have complete := andIntro93977 p afterEq combined
    have bound := compare28889 p complete
    omega
  · have beforeEq := eqIntro34748 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro94009 p guard beforeEq
    have complete := andIntro94035 p afterEq combined
    have bound := compare28890 p complete
    omega
  · have beforeEq := eqIntro34748 p pair.1
    have afterEq := eqIntro24937 p pair.2
    have combined := andIntro94009 p guard beforeEq
    have complete := andIntro94061 p afterEq combined
    have bound := compare28889 p complete
    omega
theorem local956 (p : Pattern) (guard : d310057 p = 1)
    (decreasing : bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 245 p) :
    NetHack.Sokoban22Refined85.bonus 245 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 245 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 224) + NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 224))) + bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 224) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 245 p at decreasing
  rw [gammaAfter956, at245] at decreasing
  have numeric := numeric956 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224))
  rw [oldBefore245, at245, literal, oldAfter956, gammaAfter956]
  exact numeric
theorem numeric957 (p : Pattern) (guard : d287735 p = 1) (decreasing : d33212 p < d42245 p) :
    d51138 p + d42245 p ≤ (0 : Int) + d50101 p + d33212 p := by
  have beforeRange := bonus_range 246 p
  rw [at246] at beforeRange
  have afterRange := bonus_range 224 (HazardPattern.afterPattern 10000 p (.walk 224))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ∧ bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) ≤ 2 at afterRange
  rw [gammaAfter957] at afterRange
  have possibilities : (d42245 p = 1 ∧ d33212 p = 0) ∨ (d42245 p = 2 ∧ d33212 p = 0) ∨ (d42245 p = 2 ∧ d33212 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro30116 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro94402 p guard beforeEq
    have complete := andIntro94680 p afterEq combined
    have bound := compare41217 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro24772 p pair.2
    have combined := andIntro94712 p guard beforeEq
    have complete := andIntro94750 p afterEq combined
    have bound := compare41218 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro24937 p pair.2
    have combined := andIntro94712 p guard beforeEq
    have complete := andIntro94788 p afterEq combined
    have bound := compare41217 p complete
    omega
theorem local957 (p : Pattern) (guard : d287735 p = 1)
    (decreasing : bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 246 p) :
    NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 246 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 224) + NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 224))) + bonus 224 (HazardPattern.afterPattern 10000 p (.walk 224)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 224) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224)) < bonus 246 p at decreasing
  rw [gammaAfter957, at246] at decreasing
  have numeric := numeric957 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 224)) (HazardPattern.afterPattern 10000 p (.walk 224))
  rw [oldBefore246, at246, literal, oldAfter957, gammaAfter957]
  exact numeric
theorem numeric958 (p : Pattern) (guard : d253272 p = 1) (decreasing : d346112 p < d42245 p) :
    d51138 p + d42245 p ≤ (2 : Int) + d47866 p + d346112 p := by
  have beforeRange := bonus_range 246 p
  rw [at246] at beforeRange
  have afterRange := bonus_range 224 (HazardPattern.afterPattern 10000 p (.push 224 (.stay 202)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 224 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 202))) ∧ bonus (HazardPattern.nextHero (.push 224 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 202))) ≤ 2 at afterRange
  rw [gammaAfter958] at afterRange
  have possibilities : (d42245 p = 1 ∧ d346112 p = 0) ∨ (d42245 p = 2 ∧ d346112 p = 0) ∨ (d42245 p = 2 ∧ d346112 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro30116 p pair.1
    have afterEq := eqIntro36480 p pair.2
    have combined := andIntro95127 p guard beforeEq
    have complete := andIntro95421 p afterEq combined
    have bound := compare42321 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro36480 p pair.2
    have combined := andIntro95453 p guard beforeEq
    have complete := andIntro95497 p afterEq combined
    have bound := compare42879 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro36590 p pair.2
    have combined := andIntro95453 p guard beforeEq
    have complete := andIntro95541 p combined afterEq
    have bound := compare41219 p complete
    omega
theorem local958 (p : Pattern) (guard : d253272 p = 1)
    (decreasing : bonus 224 (HazardPattern.afterPattern 10000 p (.push 224 (.stay 202))) < bonus 246 p) :
    NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 246 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 224 (.stay 202)) + NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 224 (.stay 202)))) + bonus 224 (HazardPattern.afterPattern 10000 p (.push 224 (.stay 202))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 224 (.stay 202)) = (2 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 224 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 202))) < bonus 246 p at decreasing
  rw [gammaAfter958, at246] at decreasing
  have numeric := numeric958 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 224 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 224 (.stay 202)))
  rw [oldBefore246, at246, literal, oldAfter958, gammaAfter958]
  exact numeric
theorem numeric959 (p : Pattern) (guard : d271214 p = 1) (decreasing : d44879 p < d42245 p) :
    d51138 p + d42245 p ≤ (0 : Int) + d51635 p + d44879 p := by
  have beforeRange := bonus_range 246 p
  rw [at246] at beforeRange
  have afterRange := bonus_range 247 (HazardPattern.afterPattern 10000 p (.walk 247))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) ∧ bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) ≤ 2 at afterRange
  rw [gammaAfter959] at afterRange
  have possibilities : (d42245 p = 1 ∧ d44879 p = 0) ∨ (d42245 p = 2 ∧ d44879 p = 0) ∨ (d42245 p = 2 ∧ d44879 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro30116 p pair.1
    have afterEq := eqIntro31994 p pair.2
    have combined := andIntro95887 p guard beforeEq
    have complete := andIntro96221 p afterEq combined
    have bound := compare42880 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro31994 p pair.2
    have combined := andIntro96253 p guard beforeEq
    have complete := andIntro96297 p afterEq combined
    have bound := compare42881 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro32161 p pair.2
    have combined := andIntro96253 p guard beforeEq
    have complete := andIntro96341 p afterEq combined
    have bound := compare42880 p complete
    omega
theorem local959 (p : Pattern) (guard : d271214 p = 1)
    (decreasing : bonus 247 (HazardPattern.afterPattern 10000 p (.walk 247)) < bonus 246 p) :
    NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 246 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 247) + NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 247))) + bonus 247 (HazardPattern.afterPattern 10000 p (.walk 247)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 247) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247)) < bonus 246 p at decreasing
  rw [gammaAfter959, at246] at decreasing
  have numeric := numeric959 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 247)) (HazardPattern.afterPattern 10000 p (.walk 247))
  rw [oldBefore246, at246, literal, oldAfter959, gammaAfter959]
  exact numeric
theorem numeric960 (p : Pattern) (guard : d46864 p = 1) (decreasing : d354132 p < d42245 p) :
    d51138 p + d42245 p ≤ (0 : Int) + d351900 p + d354132 p := by
  have beforeRange := bonus_range 246 p
  rw [at246] at beforeRange
  have afterRange := bonus_range 247 (HazardPattern.afterPattern 10000 p (.push 247 (.stay 248)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 247 (.stay 248))) (HazardPattern.afterPattern 10000 p (.push 247 (.stay 248))) ∧ bonus (HazardPattern.nextHero (.push 247 (.stay 248))) (HazardPattern.afterPattern 10000 p (.push 247 (.stay 248))) ≤ 2 at afterRange
  rw [gammaAfter960] at afterRange
  have possibilities : (d42245 p = 1 ∧ d354132 p = 0) ∨ (d42245 p = 2 ∧ d354132 p = 0) ∨ (d42245 p = 2 ∧ d354132 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro30116 p pair.1
    have afterEq := eqIntro36989 p pair.2
    have combined := andIntro96716 p guard beforeEq
    have complete := andIntro96939 p afterEq combined
    have bound := compare42882 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro36989 p pair.2
    have combined := andIntro96972 p guard beforeEq
    have complete := andIntro97010 p afterEq combined
    have bound := compare42883 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro37136 p pair.2
    have combined := andIntro96972 p guard beforeEq
    have complete := andIntro97048 p combined afterEq
    have bound := compare42882 p complete
    omega
theorem local960 (p : Pattern) (guard : d46864 p = 1)
    (decreasing : bonus 247 (HazardPattern.afterPattern 10000 p (.push 247 (.stay 248))) < bonus 246 p) :
    NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 246 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 247 (.stay 248)) + NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 247 (.stay 248)))) + bonus 247 (HazardPattern.afterPattern 10000 p (.push 247 (.stay 248))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 247 (.stay 248)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 247 (.stay 248))) (HazardPattern.afterPattern 10000 p (.push 247 (.stay 248))) < bonus 246 p at decreasing
  rw [gammaAfter960, at246] at decreasing
  have numeric := numeric960 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 247 (.stay 248))) (HazardPattern.afterPattern 10000 p (.push 247 (.stay 248)))
  rw [oldBefore246, at246, literal, oldAfter960, gammaAfter960]
  exact numeric
theorem numeric961 (p : Pattern) (guard : d338547 p = 1) (decreasing : d40148 p < d42245 p) :
    d51138 p + d42245 p ≤ (0 : Int) + d47866 p + d40148 p := by
  have beforeRange := bonus_range 246 p
  rw [at246] at beforeRange
  have afterRange := bonus_range 245 (HazardPattern.afterPattern 10000 p (.walk 245))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 245)) (HazardPattern.afterPattern 10000 p (.walk 245)) ∧ bonus (HazardPattern.nextHero (.walk 245)) (HazardPattern.afterPattern 10000 p (.walk 245)) ≤ 2 at afterRange
  rw [gammaAfter961] at afterRange
  have possibilities : (d42245 p = 1 ∧ d40148 p = 0) ∨ (d42245 p = 2 ∧ d40148 p = 0) ∨ (d42245 p = 2 ∧ d40148 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro30116 p pair.1
    have afterEq := eqIntro28987 p pair.2
    have combined := andIntro97049 p beforeEq guard
    have complete := andIntro97326 p afterEq combined
    have bound := compare42884 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro28987 p pair.2
    have combined := andIntro97327 p guard beforeEq
    have complete := andIntro97365 p afterEq combined
    have bound := compare42885 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro29076 p pair.2
    have combined := andIntro97327 p guard beforeEq
    have complete := andIntro97403 p afterEq combined
    have bound := compare42884 p complete
    omega
theorem local961 (p : Pattern) (guard : d338547 p = 1)
    (decreasing : bonus 245 (HazardPattern.afterPattern 10000 p (.walk 245)) < bonus 246 p) :
    NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 246 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 245) + NetHack.Sokoban22Refined85.bonus 245 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 245))) + bonus 245 (HazardPattern.afterPattern 10000 p (.walk 245)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 245) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 245)) (HazardPattern.afterPattern 10000 p (.walk 245)) < bonus 246 p at decreasing
  rw [gammaAfter961, at246] at decreasing
  have numeric := numeric961 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 245)) (HazardPattern.afterPattern 10000 p (.walk 245))
  rw [oldBefore246, at246, literal, oldAfter961, gammaAfter961]
  exact numeric
theorem numeric962 (p : Pattern) (guard : d322255 p = 1) (decreasing : d36004 p < d42245 p) :
    d51138 p + d42245 p ≤ (0 : Int) + d50493 p + d36004 p := by
  have beforeRange := bonus_range 246 p
  rw [at246] at beforeRange
  have afterRange := bonus_range 225 (HazardPattern.afterPattern 10000 p (.walk 225))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ∧ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ≤ 2 at afterRange
  rw [gammaAfter962] at afterRange
  have possibilities : (d42245 p = 1 ∧ d36004 p = 0) ∨ (d42245 p = 2 ∧ d36004 p = 0) ∨ (d42245 p = 2 ∧ d36004 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro30116 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro97745 p beforeEq guard
    have complete := andIntro98091 p afterEq combined
    have bound := compare42886 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro98123 p guard beforeEq
    have complete := andIntro98172 p afterEq combined
    have bound := compare42887 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro26978 p pair.2
    have combined := andIntro98123 p guard beforeEq
    have complete := andIntro98216 p afterEq combined
    have bound := compare42886 p complete
    omega
theorem local962 (p : Pattern) (guard : d322255 p = 1)
    (decreasing : bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 246 p) :
    NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 246 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 225) + NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 225))) + bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 225) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 246 p at decreasing
  rw [gammaAfter962, at246] at decreasing
  have numeric := numeric962 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225))
  rw [oldBefore246, at246, literal, oldAfter962, gammaAfter962]
  exact numeric
theorem numeric963 (p : Pattern) (guard : d287737 p = 1) (decreasing : d30634 p < d42245 p) :
    d51138 p + d42245 p ≤ (0 : Int) + d47866 p + d30634 p := by
  have beforeRange := bonus_range 246 p
  rw [at246] at beforeRange
  have afterRange := bonus_range 223 (HazardPattern.afterPattern 10000 p (.walk 223))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) ∧ bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) ≤ 2 at afterRange
  rw [gammaAfter963] at afterRange
  have possibilities : (d42245 p = 1 ∧ d30634 p = 0) ∨ (d42245 p = 2 ∧ d30634 p = 0) ∨ (d42245 p = 2 ∧ d30634 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro30116 p pair.1
    have afterEq := eqIntro23817 p pair.2
    have combined := andIntro98398 p guard beforeEq
    have complete := andIntro98517 p afterEq combined
    have bound := compare42884 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro23817 p pair.2
    have combined := andIntro98537 p guard beforeEq
    have complete := andIntro98557 p afterEq combined
    have bound := compare42885 p complete
    omega
  · have beforeEq := eqIntro36184 p pair.1
    have afterEq := eqIntro23933 p pair.2
    have combined := andIntro98537 p guard beforeEq
    have complete := andIntro98577 p afterEq combined
    have bound := compare42884 p complete
    omega
theorem local963 (p : Pattern) (guard : d287737 p = 1)
    (decreasing : bonus 223 (HazardPattern.afterPattern 10000 p (.walk 223)) < bonus 246 p) :
    NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 246 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 223) + NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 223))) + bonus 223 (HazardPattern.afterPattern 10000 p (.walk 223)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 223) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223)) < bonus 246 p at decreasing
  rw [gammaAfter963, at246] at decreasing
  have numeric := numeric963 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 223)) (HazardPattern.afterPattern 10000 p (.walk 223))
  rw [oldBefore246, at246, literal, oldAfter963, gammaAfter963]
  exact numeric
theorem numeric964 (p : Pattern) (guard : d310774 p = 1) (decreasing : d36004 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50493 p + d36004 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 225 (HazardPattern.afterPattern 10000 p (.walk 225))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ∧ bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) ≤ 2 at afterRange
  rw [gammaAfter964] at afterRange
  have possibilities : (d44879 p = 1 ∧ d36004 p = 0) ∨ (d44879 p = 2 ∧ d36004 p = 0) ∨ (d44879 p = 2 ∧ d36004 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro98861 p beforeEq guard
    have complete := andIntro99207 p afterEq combined
    have bound := compare42888 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro26799 p pair.2
    have combined := andIntro99235 p guard beforeEq
    have complete := andIntro99285 p afterEq combined
    have bound := compare42889 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro26978 p pair.2
    have combined := andIntro99235 p guard beforeEq
    have complete := andIntro99329 p afterEq combined
    have bound := compare42888 p complete
    omega
theorem local964 (p : Pattern) (guard : d310774 p = 1)
    (decreasing : bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 225) + NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 225))) + bonus 225 (HazardPattern.afterPattern 10000 p (.walk 225)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 225) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225)) < bonus 247 p at decreasing
  rw [gammaAfter964, at247] at decreasing
  have numeric := numeric964 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 225)) (HazardPattern.afterPattern 10000 p (.walk 225))
  rw [oldBefore247, at247, literal, oldAfter964, gammaAfter964]
  exact numeric
theorem numeric965 (p : Pattern) (guard : d14 p = 1) (decreasing : d47282 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d47282 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.walk 248))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248)) ∧ bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248)) ≤ 2 at afterRange
  rw [gammaAfter965] at afterRange
  have possibilities : (d44879 p = 1 ∧ d47282 p = 0) ∨ (d44879 p = 2 ∧ d47282 p = 0) ∨ (d44879 p = 2 ∧ d47282 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro99680 p guard beforeEq
    have complete := andIntro99893 p afterEq combined
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro33432 p pair.2
    have combined := andIntro99925 p guard beforeEq
    have complete := andIntro99957 p afterEq combined
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro33595 p pair.2
    have combined := andIntro99925 p guard beforeEq
    have complete := andIntro99989 p afterEq combined
    have bound := compare42890 p complete
    omega
theorem local965 (p : Pattern) (guard : d14 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.walk 248)) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 248) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 248))) + bonus 248 (HazardPattern.afterPattern 10000 p (.walk 248)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 248) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248)) < bonus 247 p at decreasing
  rw [gammaAfter965, at247] at decreasing
  have numeric := numeric965 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 248)) (HazardPattern.afterPattern 10000 p (.walk 248))
  rw [oldBefore247, at247, literal, oldAfter965, gammaAfter965]
  exact numeric
theorem numeric966 (p : Pattern) (guard : d358937 p = 1) (decreasing : d361190 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d361190 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 250)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 248 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 250))) ∧ bonus (HazardPattern.nextHero (.push 248 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 250))) ≤ 2 at afterRange
  rw [gammaAfter966] at afterRange
  have possibilities : (d44879 p = 1 ∧ d361190 p = 0) ∨ (d44879 p = 2 ∧ d361190 p = 0) ∨ (d44879 p = 2 ∧ d361190 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro37999 p pair.2
    have combined := andIntro99997 p beforeEq guard
    have complete := andIntro100065 p afterEq combined
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro37999 p pair.2
    have combined := andIntro100073 p beforeEq guard
    have complete := andIntro100087 p afterEq combined
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38147 p pair.2
    have combined := andIntro100073 p beforeEq guard
    have complete := andIntro100101 p combined afterEq
    have bound := compare42890 p complete
    omega
theorem local966 (p : Pattern) (guard : d358937 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 250))) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 250)) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 250)))) + bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 250))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 250)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 248 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 250))) < bonus 247 p at decreasing
  rw [gammaAfter966, at247] at decreasing
  have numeric := numeric966 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 248 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 250)))
  rw [oldBefore247, at247, literal, oldAfter966, gammaAfter966]
  exact numeric
theorem numeric967 (p : Pattern) (guard : d363235 p = 1) (decreasing : d363279 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d363279 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 251)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 248 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 251))) ∧ bonus (HazardPattern.nextHero (.push 248 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 251))) ≤ 2 at afterRange
  rw [gammaAfter967] at afterRange
  have possibilities : (d44879 p = 1 ∧ d363279 p = 0) ∨ (d44879 p = 2 ∧ d363279 p = 0) ∨ (d44879 p = 2 ∧ d363279 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro38155 p pair.2
    have combined := andIntro100177 p beforeEq guard
    have complete := andIntro100257 p afterEq combined
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38155 p pair.2
    have combined := andIntro100269 p beforeEq guard
    have complete := andIntro100283 p afterEq combined
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38163 p pair.2
    have combined := andIntro100269 p beforeEq guard
    have complete := andIntro100297 p combined afterEq
    have bound := compare42890 p complete
    omega
theorem local967 (p : Pattern) (guard : d363235 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 251))) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 251)) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 251)))) + bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 251))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 251)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 248 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 251))) < bonus 247 p at decreasing
  rw [gammaAfter967, at247] at decreasing
  have numeric := numeric967 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 248 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 251)))
  rw [oldBefore247, at247, literal, oldAfter967, gammaAfter967]
  exact numeric
theorem numeric968 (p : Pattern) (guard : d363819 p = 1) (decreasing : d363864 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d363864 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 252)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 248 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 252))) ∧ bonus (HazardPattern.nextHero (.push 248 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 252))) ≤ 2 at afterRange
  rw [gammaAfter968] at afterRange
  have possibilities : (d44879 p = 1 ∧ d363864 p = 0) ∨ (d44879 p = 2 ∧ d363864 p = 0) ∨ (d44879 p = 2 ∧ d363864 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro38171 p pair.2
    have combined := andIntro100379 p beforeEq guard
    have complete := andIntro100443 p afterEq combined
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38171 p pair.2
    have combined := andIntro100455 p beforeEq guard
    have complete := andIntro100469 p afterEq combined
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38179 p pair.2
    have combined := andIntro100455 p beforeEq guard
    have complete := andIntro100483 p combined afterEq
    have bound := compare42890 p complete
    omega
theorem local968 (p : Pattern) (guard : d363819 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 252))) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 252)) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 252)))) + bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 252))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 252)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 248 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 252))) < bonus 247 p at decreasing
  rw [gammaAfter968, at247] at decreasing
  have numeric := numeric968 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 248 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 252)))
  rw [oldBefore247, at247, literal, oldAfter968, gammaAfter968]
  exact numeric
theorem numeric969 (p : Pattern) (guard : d364421 p = 1) (decreasing : d364467 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d364467 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 253)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 248 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 253))) ∧ bonus (HazardPattern.nextHero (.push 248 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 253))) ≤ 2 at afterRange
  rw [gammaAfter969] at afterRange
  have possibilities : (d44879 p = 1 ∧ d364467 p = 0) ∨ (d44879 p = 2 ∧ d364467 p = 0) ∨ (d44879 p = 2 ∧ d364467 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro38187 p pair.2
    have combined := andIntro100547 p beforeEq guard
    have complete := andIntro100606 p afterEq combined
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38187 p pair.2
    have combined := andIntro100618 p beforeEq guard
    have complete := andIntro100632 p afterEq combined
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38195 p pair.2
    have combined := andIntro100618 p beforeEq guard
    have complete := andIntro100646 p combined afterEq
    have bound := compare42890 p complete
    omega
theorem local969 (p : Pattern) (guard : d364421 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 253))) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 253)) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 253)))) + bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 253))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 253)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 248 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 253))) < bonus 247 p at decreasing
  rw [gammaAfter969, at247] at decreasing
  have numeric := numeric969 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 248 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 253)))
  rw [oldBefore247, at247, literal, oldAfter969, gammaAfter969]
  exact numeric
theorem numeric970 (p : Pattern) (guard : d364965 p = 1) (decreasing : d365012 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d365012 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 254)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 248 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 254))) ∧ bonus (HazardPattern.nextHero (.push 248 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 254))) ≤ 2 at afterRange
  rw [gammaAfter970] at afterRange
  have possibilities : (d44879 p = 1 ∧ d365012 p = 0) ∨ (d44879 p = 2 ∧ d365012 p = 0) ∨ (d44879 p = 2 ∧ d365012 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro38203 p pair.2
    have combined := andIntro100705 p beforeEq guard
    have complete := andIntro100751 p afterEq combined
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38203 p pair.2
    have combined := andIntro100763 p beforeEq guard
    have complete := andIntro100777 p afterEq combined
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38211 p pair.2
    have combined := andIntro100763 p beforeEq guard
    have complete := andIntro100791 p combined afterEq
    have bound := compare42890 p complete
    omega
theorem local970 (p : Pattern) (guard : d364965 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 254))) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 254)) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 254)))) + bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 254))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 254)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 248 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 254))) < bonus 247 p at decreasing
  rw [gammaAfter970, at247] at decreasing
  have numeric := numeric970 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 248 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 254)))
  rw [oldBefore247, at247, literal, oldAfter970, gammaAfter970]
  exact numeric
theorem numeric971 (p : Pattern) (guard : d365448 p = 1) (decreasing : d365496 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d365496 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 255)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 248 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 255))) ∧ bonus (HazardPattern.nextHero (.push 248 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 255))) ≤ 2 at afterRange
  rw [gammaAfter971] at afterRange
  have possibilities : (d44879 p = 1 ∧ d365496 p = 0) ∨ (d44879 p = 2 ∧ d365496 p = 0) ∨ (d44879 p = 2 ∧ d365496 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro38220 p pair.2
    have combined := andIntro100837 p beforeEq guard
    have complete := andIntro100853 p afterEq combined
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38220 p pair.2
    have combined := andIntro100865 p beforeEq guard
    have complete := andIntro100879 p afterEq combined
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38229 p pair.2
    have combined := andIntro100865 p beforeEq guard
    have complete := andIntro100893 p combined afterEq
    have bound := compare42890 p complete
    omega
theorem local971 (p : Pattern) (guard : d365448 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 255))) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 255)) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 255)))) + bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 255))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 255)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 248 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 255))) < bonus 247 p at decreasing
  rw [gammaAfter971, at247] at decreasing
  have numeric := numeric971 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 248 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 255)))
  rw [oldBefore247, at247, literal, oldAfter971, gammaAfter971]
  exact numeric
theorem numeric972 (p : Pattern) (guard : d365809 p = 1) (decreasing : d365858 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d365858 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 256)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 248 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 256))) ∧ bonus (HazardPattern.nextHero (.push 248 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 256))) ≤ 2 at afterRange
  rw [gammaAfter972] at afterRange
  have possibilities : (d44879 p = 1 ∧ d365858 p = 0) ∨ (d44879 p = 2 ∧ d365858 p = 0) ∨ (d44879 p = 2 ∧ d365858 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro38238 p pair.2
    have combined := andIntro100909 p beforeEq guard
    have complete := andIntro100923 p afterEq combined
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38238 p pair.2
    have combined := andIntro100933 p beforeEq guard
    have complete := andIntro100934 p combined afterEq
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro38239 p pair.2
    have combined := andIntro100933 p beforeEq guard
    have complete := andIntro100935 p combined afterEq
    have bound := compare42890 p complete
    omega
theorem local972 (p : Pattern) (guard : d365809 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 256))) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 256)) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 256)))) + bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 256))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 256)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 248 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 256))) < bonus 247 p at decreasing
  rw [gammaAfter972, at247] at decreasing
  have numeric := numeric972 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 248 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 256)))
  rw [oldBefore247, at247, literal, oldAfter972, gammaAfter972]
  exact numeric
theorem numeric973 (p : Pattern) (guard : d366034 p = 1) (decreasing : d0 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 257)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 248 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 257))) ∧ bonus (HazardPattern.nextHero (.push 248 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 257))) ≤ 2 at afterRange
  rw [gammaAfter973] at afterRange
  have possibilities : (d44879 p = 1 ∧ d0 p = 0) ∨ (d44879 p = 2 ∧ d0 p = 0) ∨ (d44879 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro100949 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro100958 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro100958 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare42890 p complete
    omega
theorem local973 (p : Pattern) (guard : d366034 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 257))) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 257)) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 257)))) + bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 257))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 257)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 248 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 257))) < bonus 247 p at decreasing
  rw [gammaAfter973, at247] at decreasing
  have numeric := numeric973 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 248 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 257)))
  rw [oldBefore247, at247, literal, oldAfter973, gammaAfter973]
  exact numeric
theorem numeric974 (p : Pattern) (guard : d366084 p = 1) (decreasing : d0 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 258)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 248 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 258))) ∧ bonus (HazardPattern.nextHero (.push 248 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 258))) ≤ 2 at afterRange
  rw [gammaAfter974] at afterRange
  have possibilities : (d44879 p = 1 ∧ d0 p = 0) ∨ (d44879 p = 2 ∧ d0 p = 0) ∨ (d44879 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro100967 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro100976 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro100976 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare42890 p complete
    omega
theorem local974 (p : Pattern) (guard : d366084 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 258))) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 258)) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 258)))) + bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 258))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 258)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 248 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 258))) < bonus 247 p at decreasing
  rw [gammaAfter974, at247] at decreasing
  have numeric := numeric974 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 248 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 258)))
  rw [oldBefore247, at247, literal, oldAfter974, gammaAfter974]
  exact numeric
theorem numeric975 (p : Pattern) (guard : d366139 p = 1) (decreasing : d0 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 259)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 248 (.fill 259))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 259))) ∧ bonus (HazardPattern.nextHero (.push 248 (.fill 259))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 259))) ≤ 2 at afterRange
  rw [gammaAfter975] at afterRange
  have possibilities : (d44879 p = 1 ∧ d0 p = 0) ∨ (d44879 p = 2 ∧ d0 p = 0) ∨ (d44879 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro100985 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro100994 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro100994 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare42890 p complete
    omega
theorem local975 (p : Pattern) (guard : d366139 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 259))) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 259)) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 259)))) + bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 259))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 259)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 248 (.fill 259))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 259))) < bonus 247 p at decreasing
  rw [gammaAfter975, at247] at decreasing
  have numeric := numeric975 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 248 (.fill 259))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 259)))
  rw [oldBefore247, at247, literal, oldAfter975, gammaAfter975]
  exact numeric
theorem numeric976 (p : Pattern) (guard : d366199 p = 1) (decreasing : d0 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d0 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 260)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 248 (.fill 260))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 260))) ∧ bonus (HazardPattern.nextHero (.push 248 (.fill 260))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 260))) ≤ 2 at afterRange
  rw [gammaAfter976] at afterRange
  have possibilities : (d44879 p = 1 ∧ d0 p = 0) ∨ (d44879 p = 2 ∧ d0 p = 0) ∨ (d44879 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro101003 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro101012 p beforeEq guard
    have complete := andIntro767 p combined afterEq
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro101012 p beforeEq guard
    have complete := andIntro769 p afterEq afterEq
    have bound := compare42890 p complete
    omega
theorem local976 (p : Pattern) (guard : d366199 p = 1)
    (decreasing : bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 260))) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 260)) + NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 260)))) + bonus 248 (HazardPattern.afterPattern 10000 p (.push 248 (.fill 260))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 248 (.fill 260)) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 248 (.fill 260))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 260))) < bonus 247 p at decreasing
  rw [gammaAfter976, at247] at decreasing
  have numeric := numeric976 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 248 (.fill 260))) (HazardPattern.afterPattern 10000 p (.push 248 (.fill 260)))
  rw [oldBefore247, at247, literal, oldAfter976, gammaAfter976]
  exact numeric
theorem numeric977 (p : Pattern) (guard : d271214 p = 1) (decreasing : d42245 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d51138 p + d42245 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 246 (HazardPattern.afterPattern 10000 p (.walk 246))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) ∧ bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) ≤ 2 at afterRange
  rw [gammaAfter977] at afterRange
  have possibilities : (d44879 p = 1 ∧ d42245 p = 0) ∨ (d44879 p = 2 ∧ d42245 p = 0) ∨ (d44879 p = 2 ∧ d42245 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro29978 p pair.2
    have combined := andIntro101360 p guard beforeEq
    have complete := andIntro101688 p afterEq combined
    have bound := compare42892 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro29978 p pair.2
    have combined := andIntro101720 p guard beforeEq
    have complete := andIntro101764 p afterEq combined
    have bound := compare42893 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro30116 p pair.2
    have combined := andIntro101720 p guard beforeEq
    have complete := andIntro101808 p afterEq combined
    have bound := compare42892 p complete
    omega
theorem local977 (p : Pattern) (guard : d271214 p = 1)
    (decreasing : bonus 246 (HazardPattern.afterPattern 10000 p (.walk 246)) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 246) + NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 246))) + bonus 246 (HazardPattern.afterPattern 10000 p (.walk 246)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 246) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246)) < bonus 247 p at decreasing
  rw [gammaAfter977, at247] at decreasing
  have numeric := numeric977 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 246)) (HazardPattern.afterPattern 10000 p (.walk 246))
  rw [oldBefore247, at247, literal, oldAfter977, gammaAfter977]
  exact numeric
theorem numeric978 (p : Pattern) (guard : d338652 p = 1) (decreasing : d0 p < d44879 p) :
    d51635 p + d44879 p ≤ (9 : Int) + d338883 p + d0 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 246 (HazardPattern.afterPattern 10000 p (.push 246 (.stay 245)))
  change 0 ≤ bonus (HazardPattern.nextHero (.push 246 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 246 (.stay 245))) ∧ bonus (HazardPattern.nextHero (.push 246 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 246 (.stay 245))) ≤ 2 at afterRange
  rw [gammaAfter978] at afterRange
  have possibilities : (d44879 p = 1 ∧ d0 p = 0) ∨ (d44879 p = 2 ∧ d0 p = 0) ∨ (d44879 p = 2 ∧ d0 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro102144 p beforeEq guard
    have complete := andIntro102145 p afterEq combined
    have bound := compare45259 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro1383 p pair.2
    have combined := andIntro102177 p guard beforeEq
    have complete := andIntro102178 p afterEq combined
    have bound := compare46641 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro1384 p pair.2
    have combined := andIntro102177 p guard beforeEq
    have complete := andIntro102179 p afterEq combined
    have bound := compare42894 p complete
    omega
theorem local978 (p : Pattern) (guard : d338652 p = 1)
    (decreasing : bonus 246 (HazardPattern.afterPattern 10000 p (.push 246 (.stay 245))) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.push 246 (.stay 245)) + NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 246 (.stay 245)))) + bonus 246 (HazardPattern.afterPattern 10000 p (.push 246 (.stay 245))) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.push 246 (.stay 245)) = (9 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.push 246 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 246 (.stay 245))) < bonus 247 p at decreasing
  rw [gammaAfter978, at247] at decreasing
  have numeric := numeric978 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.push 246 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 246 (.stay 245)))
  rw [oldBefore247, at247, literal, oldAfter978, gammaAfter978]
  exact numeric
theorem numeric979 (p : Pattern) (guard : d331335 p = 1) (decreasing : d38812 p < d44879 p) :
    d51635 p + d44879 p ≤ (0 : Int) + d50823 p + d38812 p := by
  have beforeRange := bonus_range 247 p
  rw [at247] at beforeRange
  have afterRange := bonus_range 226 (HazardPattern.afterPattern 10000 p (.walk 226))
  change 0 ≤ bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) ∧ bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) ≤ 2 at afterRange
  rw [gammaAfter979] at afterRange
  have possibilities : (d44879 p = 1 ∧ d38812 p = 0) ∨ (d44879 p = 2 ∧ d38812 p = 0) ∨ (d44879 p = 2 ∧ d38812 p = 1) := by omega
  rcases possibilities with pair | pair | pair
  · have beforeEq := eqIntro32161 p pair.1
    have afterEq := eqIntro27657 p pair.2
    have combined := andIntro102525 p beforeEq guard
    have complete := andIntro102873 p afterEq combined
    have bound := compare42890 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro27657 p pair.2
    have combined := andIntro102905 p guard beforeEq
    have complete := andIntro102957 p afterEq combined
    have bound := compare42891 p complete
    omega
  · have beforeEq := eqIntro37596 p pair.1
    have afterEq := eqIntro27833 p pair.2
    have combined := andIntro102905 p guard beforeEq
    have complete := andIntro103001 p afterEq combined
    have bound := compare42890 p complete
    omega
theorem local979 (p : Pattern) (guard : d331335 p = 1)
    (decreasing : bonus 226 (HazardPattern.afterPattern 10000 p (.walk 226)) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential (.walk 226) + NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 226))) + bonus 226 (HazardPattern.afterPattern 10000 p (.walk 226)) := by
  have literal : HazardPattern.slack Generated.soko2_2Potential (.walk 226) = (0 : Int) := by decide +kernel
  change bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226)) < bonus 247 p at decreasing
  rw [gammaAfter979, at247] at decreasing
  have numeric := numeric979 p guard decreasing
  change _ ≤ _ + _ + bonus (HazardPattern.nextHero (.walk 226)) (HazardPattern.afterPattern 10000 p (.walk 226))
  rw [oldBefore247, at247, literal, oldAfter979, gammaAfter979]
  exact numeric
end NetHack.Soko22Hazard87
