import NetHack.Soko22Hazard87.OracleCover027Part3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover965 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 245 .northWest = some outcome) :
    OracleCovered rowCases965 p outcome := by
  cases h245 : p 245 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 245 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_north, advanceAt245_west, advanceAt245_northWest, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt245_northWest, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 245 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_north, advanceAt245_west, advanceAt245_northWest, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt245_northWest, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover966 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 245 .southEast = some outcome) :
    OracleCovered rowCases966 p outcome := by
  cases h245 : p 245 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 245 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_south, advanceAt245_east, advanceAt245_southEast, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt245_southEast, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 245 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_south, advanceAt245_east, advanceAt245_southEast, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt245_southEast, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover967 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 245 .southWest = some outcome) :
    OracleCovered rowCases967 p outcome := by
  cases h245 : p 245 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 245 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_south, advanceAt245_west, advanceAt245_southWest, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt245_southWest, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 245 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_south, advanceAt245_west, advanceAt245_southWest, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt245_southWest, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover968 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .north = some outcome) :
    OracleCovered rowCases968 p outcome := by
  cases h246 : p 246 with
  | false =>
    cases h224 : p 224 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .north = some (.walk 224) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt48_north, advanceAt70_north, advanceAt92_north, advanceAt114_north, advanceAt136_north, advanceAt158_north, advanceAt180_north, advanceAt202_north, advanceAt224_north, advanceAt224_south, advanceAt246_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_north, h224, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 224) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 224), d287735), oracleMember957, same, ?_⟩
      simp only [d253269, d287735, d0, d1, h224, h246, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h202 : p 202 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .north = some (.push 224 (.stay 202)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt48_north, advanceAt70_north, advanceAt92_north, advanceAt114_north, advanceAt136_north, advanceAt158_north, advanceAt180_north, advanceAt202_north, advanceAt224_north, advanceAt224_south, advanceAt246_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_north, h202, h224, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 224 (.stay 202)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 224 (.stay 202)), d253272), oracleMember958, same, ?_⟩
        simp only [d253269, d253271, d253272, d0, d1, h202, h224, h246, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt48_north, advanceAt70_north, advanceAt92_north, advanceAt114_north, advanceAt136_north, advanceAt158_north, advanceAt180_north, advanceAt202_north, advanceAt224_north, advanceAt224_south, advanceAt246_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_north, h202, h224, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt48_north, advanceAt70_north, advanceAt92_north, advanceAt114_north, advanceAt136_north, advanceAt158_north, advanceAt180_north, advanceAt202_north, advanceAt224_north, advanceAt224_south, advanceAt246_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_north, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover969 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .south = some outcome) :
    OracleCovered rowCases969 p outcome := by
  cases h246 : p 246 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_south, advanceAt268_north, advanceAt268_south, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt246_south, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_south, advanceAt268_north, advanceAt268_south, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt246_south, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko22Hazard87
