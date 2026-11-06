import NetHack.Soko22Hazard87.OracleCover000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover35 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .west = some outcome) :
    OracleCovered rowCases35 p outcome := by
  cases h30 : p 30 with
  | false =>
    cases h29 : p 29 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .west = some (.walk 29) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_east, advanceAt29_west, advanceAt30_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, cornerAt30_west, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 29) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 29), d56756), oracleMember25, same, ?_⟩
      simp only [d55883, d56756, d0, d1, h29, h30, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h28 : p 28 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .west = some (.push 29 (.stay 28)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_east, advanceAt29_west, advanceAt30_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, cornerAt30_west, h28, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 29 (.stay 28)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 29 (.stay 28)), d55886), oracleMember26, same, ?_⟩
        simp only [d55883, d55885, d55886, d0, d1, h28, h29, h30, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_east, advanceAt29_west, advanceAt30_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, cornerAt30_west, h28, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_east, advanceAt29_west, advanceAt30_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, cornerAt30_west, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover36 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .northEast = some outcome) :
    OracleCovered rowCases36 p outcome := by
  cases h30 : p 30 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_north, advanceAt30_east, advanceAt30_northEast, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt30_northEast, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_north, advanceAt30_east, advanceAt30_northEast, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt30_northEast, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover37 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .northWest = some outcome) :
    OracleCovered rowCases37 p outcome := by
  cases h30 : p 30 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_north, advanceAt30_west, advanceAt30_northWest, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, cornerAt30_northWest, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_north, advanceAt30_west, advanceAt30_northWest, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, cornerAt30_northWest, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover38 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .southEast = some outcome) :
    OracleCovered rowCases38 p outcome := by
  cases h30 : p 30 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_east, advanceAt30_southEast, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, cornerAt30_southEast, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_east, advanceAt30_southEast, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, cornerAt30_southEast, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover39 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .southWest = some outcome) :
    OracleCovered rowCases39 p outcome := by
  cases h30 : p 30 with
  | false =>
    cases h52 : p 52 with
    | false =>
      cases h51 : p 51 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .southWest = some (.walk 51) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_west, advanceAt30_southWest, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, cornerAt30_southWest, h30, h51, h52, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 51) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 51), d57566), oracleMember27, same, ?_⟩
        simp only [d55891, d56762, d57564, d57565, d57566, d0, d1, h30, h51, h52, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_west, advanceAt30_southWest, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, cornerAt30_southWest, h30, h51, h52, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h29 : p 29 with
      | false =>
        cases h51 : p 51 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .southWest = some (.walk 51) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_west, advanceAt30_southWest, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, cornerAt30_southWest, h29, h30, h51, h52, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 51) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 51), d57566), oracleMember27, same, ?_⟩
          simp only [d55891, d56762, d57564, d57565, d57566, d0, d1, h29, h30, h51, h52, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_west, advanceAt30_southWest, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, cornerAt30_southWest, h29, h30, h51, h52, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_west, advanceAt30_southWest, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, cornerAt30_southWest, h29, h30, h52, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_west, advanceAt30_southWest, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, cornerAt30_southWest, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover40 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .north = some outcome) :
    OracleCovered rowCases40 p outcome := by
  cases h45 : p 45 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt1_north, advanceAt23_north, advanceAt23_south, advanceAt45_north, floorAt1, doorAt1, trapAt1, boxAt1, holeAt1, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, cornerAt45_north, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt1_north, advanceAt23_north, advanceAt23_south, advanceAt45_north, floorAt1, doorAt1, trapAt1, boxAt1, holeAt1, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, cornerAt45_north, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover41 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .south = some outcome) :
    OracleCovered rowCases41 p outcome := by
  cases h45 : p 45 with
  | false =>
    cases h67 : p 67 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .south = some (.walk 67) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_south, advanceAt67_north, advanceAt67_south, advanceAt89_south, advanceAt111_south, advanceAt133_south, advanceAt155_south, advanceAt177_south, advanceAt199_south, advanceAt221_south, advanceAt243_south, advanceAt265_south, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt45_south, h45, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 67) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 67), d57571), oracleMember28, same, ?_⟩
      simp only [d57570, d57571, d0, d1, h45, h67, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h89 : p 89 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .south = some (.push 67 (.stay 89)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_south, advanceAt67_north, advanceAt67_south, advanceAt89_south, advanceAt111_south, advanceAt133_south, advanceAt155_south, advanceAt177_south, advanceAt199_south, advanceAt221_south, advanceAt243_south, advanceAt265_south, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt45_south, h45, h67, h89, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 67 (.stay 89)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 67 (.stay 89)), d57576), oracleMember29, same, ?_⟩
        simp only [d57573, d57575, d57576, d0, d1, h45, h67, h89, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_south, advanceAt67_north, advanceAt67_south, advanceAt89_south, advanceAt111_south, advanceAt133_south, advanceAt155_south, advanceAt177_south, advanceAt199_south, advanceAt221_south, advanceAt243_south, advanceAt265_south, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt45_south, h45, h67, h89, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_south, advanceAt67_north, advanceAt67_south, advanceAt89_south, advanceAt111_south, advanceAt133_south, advanceAt155_south, advanceAt177_south, advanceAt199_south, advanceAt221_south, advanceAt243_south, advanceAt265_south, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt45_south, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover42 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .east = some outcome) :
    OracleCovered rowCases42 p outcome := by
  cases h45 : p 45 with
  | false =>
    cases h46 : p 46 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .east = some (.walk 46) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_east, advanceAt46_east, advanceAt46_west, advanceAt47_east, advanceAt48_east, advanceAt49_east, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt45_east, h45, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 46) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 46), d58123), oracleMember30, same, ?_⟩
      simp only [d54511, d58123, d0, d1, h45, h46, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h47 : p 47 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .east = some (.push 46 (.stay 47)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_east, advanceAt46_east, advanceAt46_west, advanceAt47_east, advanceAt48_east, advanceAt49_east, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt45_east, h45, h46, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 46 (.stay 47)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 46 (.stay 47)), d58126), oracleMember31, same, ?_⟩
        simp only [d51639, d58125, d58126, d0, d1, h45, h46, h47, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_east, advanceAt46_east, advanceAt46_west, advanceAt47_east, advanceAt48_east, advanceAt49_east, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt45_east, h45, h46, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_east, advanceAt46_east, advanceAt46_west, advanceAt47_east, advanceAt48_east, advanceAt49_east, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt45_east, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover43 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .west = some outcome) :
    OracleCovered rowCases43 p outcome := by
  cases h45 : p 45 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_east, advanceAt44_west, advanceAt45_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, cornerAt45_west, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_east, advanceAt44_west, advanceAt45_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, cornerAt45_west, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover44 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .northEast = some outcome) :
    OracleCovered rowCases44 p outcome := by
  cases h45 : p 45 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_north, advanceAt45_east, advanceAt45_northEast, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, cornerAt45_northEast, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_north, advanceAt45_east, advanceAt45_northEast, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, cornerAt45_northEast, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover45 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .northWest = some outcome) :
    OracleCovered rowCases45 p outcome := by
  cases h45 : p 45 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_north, advanceAt45_west, advanceAt45_northWest, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, cornerAt45_northWest, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_north, advanceAt45_west, advanceAt45_northWest, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, cornerAt45_northWest, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover46 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .southEast = some outcome) :
    OracleCovered rowCases46 p outcome := by
  cases h45 : p 45 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_south, advanceAt45_east, advanceAt45_southEast, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, cornerAt45_southEast, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_south, advanceAt45_east, advanceAt45_southEast, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, cornerAt45_southEast, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover47 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .southWest = some outcome) :
    OracleCovered rowCases47 p outcome := by
  cases h45 : p 45 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_south, advanceAt45_west, advanceAt45_southWest, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, cornerAt45_southWest, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt45_south, advanceAt45_west, advanceAt45_southWest, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, cornerAt45_southWest, h45, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover48 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .north = some outcome) :
    OracleCovered rowCases48 p outcome := by
  cases h46 : p 46 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt24_north, advanceAt24_south, advanceAt46_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, cornerAt46_north, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt24_north, advanceAt24_south, advanceAt46_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, cornerAt46_north, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover49 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .south = some outcome) :
    OracleCovered rowCases49 p outcome := by
  cases h46 : p 46 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_south, advanceAt68_north, advanceAt68_south, advanceAt90_south, advanceAt112_south, advanceAt134_south, advanceAt156_south, advanceAt178_south, advanceAt200_south, advanceAt222_south, advanceAt244_south, advanceAt266_south, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, cornerAt46_south, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_south, advanceAt68_north, advanceAt68_south, advanceAt90_south, advanceAt112_south, advanceAt134_south, advanceAt156_south, advanceAt178_south, advanceAt200_south, advanceAt222_south, advanceAt244_south, advanceAt266_south, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, cornerAt46_south, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover50 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .east = some outcome) :
    OracleCovered rowCases50 p outcome := by
  cases h46 : p 46 with
  | false =>
    cases h47 : p 47 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .east = some (.walk 47) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_east, advanceAt47_east, advanceAt47_west, advanceAt48_east, advanceAt49_east, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt46_east, h46, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 47) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 47), d54512), oracleMember32, same, ?_⟩
      simp only [d51639, d54512, d0, d1, h46, h47, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h48 : p 48 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .east = some (.push 47 (.stay 48)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_east, advanceAt47_east, advanceAt47_west, advanceAt48_east, advanceAt49_east, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt46_east, h46, h47, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 47 (.stay 48)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 47 (.stay 48)), d58129), oracleMember33, same, ?_⟩
        simp only [d54184, d58128, d58129, d0, d1, h46, h47, h48, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_east, advanceAt47_east, advanceAt47_west, advanceAt48_east, advanceAt49_east, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt46_east, h46, h47, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_east, advanceAt47_east, advanceAt47_west, advanceAt48_east, advanceAt49_east, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt46_east, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover51 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .west = some outcome) :
    OracleCovered rowCases51 p outcome := by
  cases h46 : p 46 with
  | false =>
    cases h45 : p 45 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .west = some (.walk 45) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_west, advanceAt45_east, advanceAt45_west, advanceAt46_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, cornerAt46_west, h45, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 45) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 45), d58123), oracleMember34, same, ?_⟩
      simp only [d54511, d58123, d0, d1, h45, h46, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_west, advanceAt45_east, advanceAt45_west, advanceAt46_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, cornerAt46_west, h45, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_west, advanceAt45_east, advanceAt45_west, advanceAt46_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, cornerAt46_west, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover52 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .northEast = some outcome) :
    OracleCovered rowCases52 p outcome := by
  cases h46 : p 46 with
  | false =>
    cases h47 : p 47 with
    | false =>
      cases h25 : p 25 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .northEast = some (.walk 25) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_north, advanceAt46_east, advanceAt46_northEast, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt46_northEast, h25, h46, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 25) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 25), d54513), oracleMember35, same, ?_⟩
        simp only [d51639, d54512, d54513, d0, d1, h25, h46, h47, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_north, advanceAt46_east, advanceAt46_northEast, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt46_northEast, h25, h46, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_north, advanceAt46_east, advanceAt46_northEast, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt46_northEast, h46, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_north, advanceAt46_east, advanceAt46_northEast, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt46_northEast, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover53 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .northWest = some outcome) :
    OracleCovered rowCases53 p outcome := by
  cases h46 : p 46 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_north, advanceAt46_west, advanceAt46_northWest, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, cornerAt46_northWest, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_north, advanceAt46_west, advanceAt46_northWest, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, cornerAt46_northWest, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover54 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .southEast = some outcome) :
    OracleCovered rowCases54 p outcome := by
  cases h46 : p 46 with
  | false =>
    cases h47 : p 47 with
    | false =>
      cases h69 : p 69 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .southEast = some (.walk 69) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_south, advanceAt46_east, advanceAt46_southEast, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt46_southEast, h46, h47, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 69) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 69), d58433), oracleMember36, same, ?_⟩
        simp only [d53867, d58432, d58433, d0, d1, h46, h47, h69, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_south, advanceAt46_east, advanceAt46_southEast, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt46_southEast, h46, h47, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_south, advanceAt46_east, advanceAt46_southEast, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt46_southEast, h46, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_south, advanceAt46_east, advanceAt46_southEast, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt46_southEast, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover55 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .southWest = some outcome) :
    OracleCovered rowCases55 p outcome := by
  cases h46 : p 46 with
  | false =>
    cases h45 : p 45 with
    | false =>
      cases h67 : p 67 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .southWest = some (.walk 67) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_south, advanceAt46_west, advanceAt46_southWest, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, cornerAt46_southWest, h45, h46, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 67) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 67), d58745), oracleMember37, same, ?_⟩
        simp only [d57570, d58744, d58745, d0, d1, h45, h46, h67, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_south, advanceAt46_west, advanceAt46_southWest, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, cornerAt46_southWest, h45, h46, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_south, advanceAt46_west, advanceAt46_southWest, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, cornerAt46_southWest, h45, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt46_south, advanceAt46_west, advanceAt46_southWest, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, cornerAt46_southWest, h46, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover56 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .north = some outcome) :
    OracleCovered rowCases56 p outcome := by
  cases h47 : p 47 with
  | false =>
    cases h25 : p 25 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .north = some (.walk 25) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt25_north, advanceAt25_south, advanceAt47_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt47_north, h25, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 25) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 25), d51640), oracleMember38, same, ?_⟩
      simp only [d51639, d51640, d0, d1, h25, h47, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt25_north, advanceAt25_south, advanceAt47_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt47_north, h25, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt25_north, advanceAt25_south, advanceAt47_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt47_north, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover57 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .south = some outcome) :
    OracleCovered rowCases57 p outcome := by
  cases h47 : p 47 with
  | false =>
    cases h69 : p 69 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .south = some (.walk 69) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_south, advanceAt69_north, advanceAt69_south, advanceAt91_south, advanceAt113_south, advanceAt135_south, advanceAt157_south, advanceAt179_south, advanceAt201_south, advanceAt223_south, advanceAt245_south, advanceAt267_south, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt47_south, h47, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 69) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 69), d58432), oracleMember39, same, ?_⟩
      simp only [d53867, d58432, d0, d1, h47, h69, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h91 : p 91 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .south = some (.push 69 (.stay 91)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_south, advanceAt69_north, advanceAt69_south, advanceAt91_south, advanceAt113_south, advanceAt135_south, advanceAt157_south, advanceAt179_south, advanceAt201_south, advanceAt223_south, advanceAt245_south, advanceAt267_south, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt47_south, h47, h69, h91, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 69 (.stay 91)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 69 (.stay 91)), d58750), oracleMember40, same, ?_⟩
        simp only [d58747, d58749, d58750, d0, d1, h47, h69, h91, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_south, advanceAt69_north, advanceAt69_south, advanceAt91_south, advanceAt113_south, advanceAt135_south, advanceAt157_south, advanceAt179_south, advanceAt201_south, advanceAt223_south, advanceAt245_south, advanceAt267_south, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt47_south, h47, h69, h91, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_south, advanceAt69_north, advanceAt69_south, advanceAt91_south, advanceAt113_south, advanceAt135_south, advanceAt157_south, advanceAt179_south, advanceAt201_south, advanceAt223_south, advanceAt245_south, advanceAt267_south, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt47_south, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover58 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .east = some outcome) :
    OracleCovered rowCases58 p outcome := by
  cases h47 : p 47 with
  | false =>
    cases h48 : p 48 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .east = some (.walk 48) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_east, advanceAt48_east, advanceAt48_west, advanceAt49_east, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt47_east, h47, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 48) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 48), d54185), oracleMember41, same, ?_⟩
      simp only [d54184, d54185, d0, d1, h47, h48, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h49 : p 49 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .east = some (.push 48 (.stay 49)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_east, advanceAt48_east, advanceAt48_west, advanceAt49_east, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt47_east, h47, h48, h49, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 48 (.stay 49)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 48 (.stay 49)), d60241), oracleMember42, same, ?_⟩
        simp only [d54517, d60240, d60241, d0, d1, h47, h48, h49, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_east, advanceAt48_east, advanceAt48_west, advanceAt49_east, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt47_east, h47, h48, h49, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_east, advanceAt48_east, advanceAt48_west, advanceAt49_east, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt47_east, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover59 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .west = some outcome) :
    OracleCovered rowCases59 p outcome := by
  cases h47 : p 47 with
  | false =>
    cases h46 : p 46 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .west = some (.walk 46) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_west, advanceAt45_west, advanceAt46_east, advanceAt46_west, advanceAt47_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt47_west, h46, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 46) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 46), d54512), oracleMember43, same, ?_⟩
      simp only [d51639, d54512, d0, d1, h46, h47, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h45 : p 45 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .west = some (.push 46 (.stay 45)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_west, advanceAt45_west, advanceAt46_east, advanceAt46_west, advanceAt47_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt47_west, h45, h46, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 46 (.stay 45)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 46 (.stay 45)), d58126), oracleMember44, same, ?_⟩
        simp only [d51639, d58125, d58126, d0, d1, h45, h46, h47, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_west, advanceAt45_west, advanceAt46_east, advanceAt46_west, advanceAt47_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt47_west, h45, h46, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_west, advanceAt45_west, advanceAt46_east, advanceAt46_west, advanceAt47_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt47_west, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover60 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .northEast = some outcome) :
    OracleCovered rowCases60 p outcome := by
  cases h47 : p 47 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_north, advanceAt47_east, advanceAt47_northEast, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt47_northEast, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_north, advanceAt47_east, advanceAt47_northEast, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt47_northEast, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover61 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .northWest = some outcome) :
    OracleCovered rowCases61 p outcome := by
  cases h47 : p 47 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_north, advanceAt47_west, advanceAt47_northWest, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt47_northWest, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_north, advanceAt47_west, advanceAt47_northWest, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt47_northWest, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover62 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .southEast = some outcome) :
    OracleCovered rowCases62 p outcome := by
  cases h47 : p 47 with
  | false =>
    cases h69 : p 69 with
    | false =>
      cases h70 : p 70 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .southEast = some (.walk 70) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_south, advanceAt47_east, advanceAt47_southEast, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt47_southEast, h47, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 70) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 70), d61360), oracleMember45, same, ?_⟩
        simp only [d61357, d61358, d61359, d61360, d0, d1, h47, h69, h70, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_south, advanceAt47_east, advanceAt47_southEast, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt47_southEast, h47, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h48 : p 48 with
      | false =>
        cases h70 : p 70 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .southEast = some (.walk 70) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_south, advanceAt47_east, advanceAt47_southEast, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt47_southEast, h47, h48, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 70) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 70), d61360), oracleMember45, same, ?_⟩
          simp only [d61357, d61358, d61359, d61360, d0, d1, h47, h48, h69, h70, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_south, advanceAt47_east, advanceAt47_southEast, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt47_southEast, h47, h48, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_south, advanceAt47_east, advanceAt47_southEast, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt47_southEast, h47, h48, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_south, advanceAt47_east, advanceAt47_southEast, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt47_southEast, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover63 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .southWest = some outcome) :
    OracleCovered rowCases63 p outcome := by
  cases h47 : p 47 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_south, advanceAt47_west, advanceAt47_southWest, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt47_southWest, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt47_south, advanceAt47_west, advanceAt47_southWest, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt47_southWest, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover64 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .north = some outcome) :
    OracleCovered rowCases64 p outcome := by
  cases h48 : p 48 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt26_south, advanceAt48_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt48_north, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt26_south, advanceAt48_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt48_north, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover65 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .south = some outcome) :
    OracleCovered rowCases65 p outcome := by
  cases h48 : p 48 with
  | false =>
    cases h70 : p 70 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .south = some (.walk 70) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_south, advanceAt70_north, advanceAt70_south, advanceAt92_south, advanceAt114_south, advanceAt136_south, advanceAt158_south, advanceAt180_south, advanceAt202_south, advanceAt224_south, advanceAt246_south, advanceAt268_south, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt48_south, h48, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 70) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 70), d61807), oracleMember46, same, ?_⟩
      simp only [d61357, d61807, d0, d1, h48, h70, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_south, advanceAt70_north, advanceAt70_south, advanceAt92_south, advanceAt114_south, advanceAt136_south, advanceAt158_south, advanceAt180_south, advanceAt202_south, advanceAt224_south, advanceAt246_south, advanceAt268_south, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt48_south, h48, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_south, advanceAt70_north, advanceAt70_south, advanceAt92_south, advanceAt114_south, advanceAt136_south, advanceAt158_south, advanceAt180_south, advanceAt202_south, advanceAt224_south, advanceAt246_south, advanceAt268_south, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt48_south, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover66 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .east = some outcome) :
    OracleCovered rowCases66 p outcome := by
  cases h48 : p 48 with
  | false =>
    cases h49 : p 49 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .east = some (.walk 49) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_east, advanceAt49_east, advanceAt49_west, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt48_east, h48, h49, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 49) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 49), d55878), oracleMember47, same, ?_⟩
      simp only [d54517, d55878, d0, d1, h48, h49, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h50 : p 50 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .east = some (.push 49 (.stay 50)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_east, advanceAt49_east, advanceAt49_west, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt48_east, h48, h49, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 49 (.stay 50)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 49 (.stay 50)), d61810), oracleMember48, same, ?_⟩
        simp only [d55754, d61809, d61810, d0, d1, h48, h49, h50, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_east, advanceAt49_east, advanceAt49_west, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt48_east, h48, h49, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_east, advanceAt49_east, advanceAt49_west, advanceAt50_east, advanceAt51_east, advanceAt52_east, advanceAt53_east, advanceAt54_east, advanceAt55_east, advanceAt56_east, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, cornerAt48_east, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover67 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .west = some outcome) :
    OracleCovered rowCases67 p outcome := by
  cases h48 : p 48 with
  | false =>
    cases h47 : p 47 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .west = some (.walk 47) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_west, advanceAt45_west, advanceAt46_west, advanceAt47_east, advanceAt47_west, advanceAt48_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt48_west, h47, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 47) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 47), d54185), oracleMember49, same, ?_⟩
      simp only [d54184, d54185, d0, d1, h47, h48, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h46 : p 46 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .west = some (.push 47 (.stay 46)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_west, advanceAt45_west, advanceAt46_west, advanceAt47_east, advanceAt47_west, advanceAt48_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt48_west, h46, h47, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 47 (.stay 46)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 47 (.stay 46)), d58129), oracleMember50, same, ?_⟩
        simp only [d54184, d58128, d58129, d0, d1, h46, h47, h48, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_west, advanceAt45_west, advanceAt46_west, advanceAt47_east, advanceAt47_west, advanceAt48_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt48_west, h46, h47, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt44_west, advanceAt45_west, advanceAt46_west, advanceAt47_east, advanceAt47_west, advanceAt48_west, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt48_west, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover68 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .northEast = some outcome) :
    OracleCovered rowCases68 p outcome := by
  cases h48 : p 48 with
  | false =>
    cases h49 : p 49 with
    | false =>
      cases h27 : p 27 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .northEast = some (.walk 27) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_north, advanceAt48_east, advanceAt48_northEast, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, cornerAt48_northEast, h27, h48, h49, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 27) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 27), d55879), oracleMember51, same, ?_⟩
        simp only [d54517, d55878, d55879, d0, d1, h27, h48, h49, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_north, advanceAt48_east, advanceAt48_northEast, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, cornerAt48_northEast, h27, h48, h49, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_north, advanceAt48_east, advanceAt48_northEast, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, cornerAt48_northEast, h48, h49, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_north, advanceAt48_east, advanceAt48_northEast, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, cornerAt48_northEast, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover69 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .northWest = some outcome) :
    OracleCovered rowCases69 p outcome := by
  cases h48 : p 48 with
  | false =>
    cases h47 : p 47 with
    | false =>
      cases h25 : p 25 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .northWest = some (.walk 25) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_north, advanceAt48_west, advanceAt48_northWest, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt48_northWest, h25, h47, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 25) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 25), d54186), oracleMember52, same, ?_⟩
        simp only [d54184, d54185, d54186, d0, d1, h25, h47, h48, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_north, advanceAt48_west, advanceAt48_northWest, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt48_northWest, h25, h47, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_north, advanceAt48_west, advanceAt48_northWest, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt48_northWest, h47, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt48_north, advanceAt48_west, advanceAt48_northWest, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt48_northWest, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko22Hazard87
