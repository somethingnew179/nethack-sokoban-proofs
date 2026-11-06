import NetHack.Soko22Hazard87.OracleCover025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover910 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 216 .southEast = some outcome) :
    OracleCovered rowCases910 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 216 .southEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_south, advanceAt216_east, advanceAt216_southEast, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, cornerAt216_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover911 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 216 .southWest = some outcome) :
    OracleCovered rowCases911 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 216 .southWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_south, advanceAt216_west, advanceAt216_southWest, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, cornerAt216_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover912 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .north = some outcome) :
    OracleCovered rowCases912 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .north = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt20_north, advanceAt42_north, advanceAt64_north, advanceAt86_north, advanceAt108_north, advanceAt130_north, advanceAt152_north, advanceAt174_north, advanceAt196_north, advanceAt196_south, advanceAt218_north, floorAt20, doorAt20, trapAt20, boxAt20, holeAt20, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover913 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .south = some outcome) :
    OracleCovered rowCases913 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .south = some (.walk 240) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt240_north, advanceAt240_south, advanceAt262_south, advanceAt284_south, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt284, doorAt284, trapAt284, boxAt284, holeAt284, cornerAt218_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 240) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 240), d1), oracleMember917, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover914 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .east = some outcome) :
    OracleCovered rowCases914 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .east = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_east, advanceAt219_east, advanceAt219_west, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover915 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .west = some outcome) :
    OracleCovered rowCases915 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .west = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt198_west, advanceAt199_west, advanceAt200_west, advanceAt201_west, advanceAt202_west, advanceAt203_west, advanceAt204_west, advanceAt205_west, advanceAt206_west, advanceAt207_west, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_west, advanceAt214_west, advanceAt215_west, advanceAt216_west, advanceAt217_east, advanceAt217_west, advanceAt218_west, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover916 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .northEast = some outcome) :
    OracleCovered rowCases916 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .northEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover917 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .northWest = some outcome) :
    OracleCovered rowCases917 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .northWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_west, advanceAt218_northWest, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover918 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .southEast = some outcome) :
    OracleCovered rowCases918 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .southEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt218_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover919 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .southWest = some outcome) :
    OracleCovered rowCases919 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 .southWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_west, advanceAt218_southWest, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, cornerAt218_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover920 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .north = some outcome) :
    OracleCovered rowCases920 p outcome := by
  cases h223 : p 223 with
  | false =>
    cases h201 : p 201 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .north = some (.walk 201) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt25_north, advanceAt47_north, advanceAt69_north, advanceAt91_north, advanceAt113_north, advanceAt135_north, advanceAt157_north, advanceAt179_north, advanceAt201_north, advanceAt201_south, advanceAt223_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, cornerAt223_north, h201, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 201) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 201), d236582), oracleMember919, same, ?_⟩
      simp only [d236581, d236582, d0, d1, h201, h223, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt25_north, advanceAt47_north, advanceAt69_north, advanceAt91_north, advanceAt113_north, advanceAt135_north, advanceAt157_north, advanceAt179_north, advanceAt201_north, advanceAt201_south, advanceAt223_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, cornerAt223_north, h201, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt25_north, advanceAt47_north, advanceAt69_north, advanceAt91_north, advanceAt113_north, advanceAt135_north, advanceAt157_north, advanceAt179_north, advanceAt201_north, advanceAt201_south, advanceAt223_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, cornerAt223_north, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover921 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .south = some outcome) :
    OracleCovered rowCases921 p outcome := by
  cases h223 : p 223 with
  | false =>
    cases h245 : p 245 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .south = some (.walk 245) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_south, advanceAt245_north, advanceAt245_south, advanceAt267_south, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt223_south, h223, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 245) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 245), d279951), oracleMember920, same, ?_⟩
      simp only [d236581, d279951, d0, d1, h223, h245, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_south, advanceAt245_north, advanceAt245_south, advanceAt267_south, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt223_south, h223, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_south, advanceAt245_north, advanceAt245_south, advanceAt267_south, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt223_south, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover922 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .east = some outcome) :
    OracleCovered rowCases922 p outcome := by
  cases h223 : p 223 with
  | false =>
    cases h224 : p 224 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .east = some (.walk 224) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_east, advanceAt224_east, advanceAt224_west, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, advanceAt234_east, advanceAt235_east, advanceAt236_east, advanceAt237_east, advanceAt238_east, advanceAt239_east, advanceAt240_east, advanceAt241_east, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt223_east, h223, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 224) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 224), d241830), oracleMember921, same, ?_⟩
      simp only [d202304, d241830, d0, d1, h223, h224, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h225 : p 225 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .east = some (.push 224 (.stay 225)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_east, advanceAt224_east, advanceAt224_west, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, advanceAt234_east, advanceAt235_east, advanceAt236_east, advanceAt237_east, advanceAt238_east, advanceAt239_east, advanceAt240_east, advanceAt241_east, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt223_east, h223, h224, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 224 (.stay 225)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 224 (.stay 225)), d282284), oracleMember922, same, ?_⟩
        simp only [d261984, d282283, d282284, d0, d1, h223, h224, h225, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_east, advanceAt224_east, advanceAt224_west, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, advanceAt234_east, advanceAt235_east, advanceAt236_east, advanceAt237_east, advanceAt238_east, advanceAt239_east, advanceAt240_east, advanceAt241_east, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt223_east, h223, h224, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_east, advanceAt224_east, advanceAt224_west, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, advanceAt234_east, advanceAt235_east, advanceAt236_east, advanceAt237_east, advanceAt238_east, advanceAt239_east, advanceAt240_east, advanceAt241_east, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt223_east, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover923 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .west = some outcome) :
    OracleCovered rowCases923 p outcome := by
  cases h223 : p 223 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_west, advanceAt221_west, advanceAt222_east, advanceAt222_west, advanceAt223_west, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, cornerAt223_west, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_west, advanceAt221_west, advanceAt222_east, advanceAt222_west, advanceAt223_west, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, cornerAt223_west, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover924 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .northEast = some outcome) :
    OracleCovered rowCases924 p outcome := by
  cases h223 : p 223 with
  | false =>
    cases h201 : p 201 with
    | false =>
      cases h202 : p 202 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .northEast = some (.walk 202) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_north, advanceAt223_east, advanceAt223_northEast, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt223_northEast, h201, h202, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 202) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 202), d266246), oracleMember923, same, ?_⟩
        simp only [d202304, d236581, d241830, d266244, d266245, d266246, d0, d1, h201, h202, h223, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_north, advanceAt223_east, advanceAt223_northEast, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt223_northEast, h201, h202, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h224 : p 224 with
      | false =>
        cases h202 : p 202 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .northEast = some (.walk 202) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_north, advanceAt223_east, advanceAt223_northEast, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt223_northEast, h201, h202, h223, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 202) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 202), d266246), oracleMember923, same, ?_⟩
          simp only [d202304, d236581, d241830, d266244, d266245, d266246, d0, d1, h201, h202, h223, h224, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_north, advanceAt223_east, advanceAt223_northEast, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt223_northEast, h201, h202, h223, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_north, advanceAt223_east, advanceAt223_northEast, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt223_northEast, h201, h223, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_north, advanceAt223_east, advanceAt223_northEast, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt223_northEast, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover925 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .northWest = some outcome) :
    OracleCovered rowCases925 p outcome := by
  cases h223 : p 223 with
  | false =>
    cases h201 : p 201 with
    | false =>
      cases h200 : p 200 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .northWest = some (.walk 200) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_north, advanceAt223_west, advanceAt223_northWest, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, cornerAt223_northWest, h200, h201, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 200) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 200), d236583), oracleMember924, same, ?_⟩
        simp only [d236581, d236582, d236583, d0, d1, h200, h201, h223, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_north, advanceAt223_west, advanceAt223_northWest, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, cornerAt223_northWest, h200, h201, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_north, advanceAt223_west, advanceAt223_northWest, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, cornerAt223_northWest, h201, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_north, advanceAt223_west, advanceAt223_northWest, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, cornerAt223_northWest, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover926 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .southEast = some outcome) :
    OracleCovered rowCases926 p outcome := by
  cases h223 : p 223 with
  | false =>
    cases h245 : p 245 with
    | false =>
      cases h246 : p 246 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .southEast = some (.walk 246) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_south, advanceAt223_east, advanceAt223_southEast, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt223_southEast, h223, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 246) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 246), d287737), oracleMember925, same, ?_⟩
        simp only [d253269, d287734, d287735, d287736, d287737, d0, d1, h223, h245, h246, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_south, advanceAt223_east, advanceAt223_southEast, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt223_southEast, h223, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h224 : p 224 with
      | false =>
        cases h246 : p 246 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .southEast = some (.walk 246) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_south, advanceAt223_east, advanceAt223_southEast, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt223_southEast, h223, h224, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 246) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 246), d287737), oracleMember925, same, ?_⟩
          simp only [d253269, d287734, d287735, d287736, d287737, d0, d1, h223, h224, h245, h246, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_south, advanceAt223_east, advanceAt223_southEast, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt223_southEast, h223, h224, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_south, advanceAt223_east, advanceAt223_southEast, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt223_southEast, h223, h224, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_south, advanceAt223_east, advanceAt223_southEast, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt223_southEast, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover927 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .southWest = some outcome) :
    OracleCovered rowCases927 p outcome := by
  cases h223 : p 223 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_south, advanceAt223_west, advanceAt223_southWest, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt223_southWest, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt223_south, advanceAt223_west, advanceAt223_southWest, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt223_southWest, h223, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover928 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .north = some outcome) :
    OracleCovered rowCases928 p outcome := by
  cases h224 : p 224 with
  | false =>
    cases h202 : p 202 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .north = some (.walk 202) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt48_north, advanceAt70_north, advanceAt92_north, advanceAt114_north, advanceAt136_north, advanceAt158_north, advanceAt180_north, advanceAt202_north, advanceAt202_south, advanceAt224_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_north, h202, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 202) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 202), d251389), oracleMember926, same, ?_⟩
      simp only [d202304, d251389, d0, d1, h202, h224, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h180 : p 180 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .north = some (.push 202 (.stay 180)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt48_north, advanceAt70_north, advanceAt92_north, advanceAt114_north, advanceAt136_north, advanceAt158_north, advanceAt180_north, advanceAt202_north, advanceAt202_south, advanceAt224_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_north, h180, h202, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 202 (.stay 180)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 202 (.stay 180)), d202307), oracleMember927, same, ?_⟩
        simp only [d202304, d202306, d202307, d0, d1, h180, h202, h224, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt48_north, advanceAt70_north, advanceAt92_north, advanceAt114_north, advanceAt136_north, advanceAt158_north, advanceAt180_north, advanceAt202_north, advanceAt202_south, advanceAt224_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_north, h180, h202, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt48_north, advanceAt70_north, advanceAt92_north, advanceAt114_north, advanceAt136_north, advanceAt158_north, advanceAt180_north, advanceAt202_north, advanceAt202_south, advanceAt224_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_north, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover929 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .south = some outcome) :
    OracleCovered rowCases929 p outcome := by
  cases h224 : p 224 with
  | false =>
    cases h246 : p 246 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .south = some (.walk 246) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt246_north, advanceAt246_south, advanceAt268_south, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt224_south, h224, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 246) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 246), d287735), oracleMember928, same, ?_⟩
      simp only [d253269, d287735, d0, d1, h224, h246, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt246_north, advanceAt246_south, advanceAt268_south, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt224_south, h224, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt246_north, advanceAt246_south, advanceAt268_south, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt224_south, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover930 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .east = some outcome) :
    OracleCovered rowCases930 p outcome := by
  cases h224 : p 224 with
  | false =>
    cases h225 : p 225 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .east = some (.walk 225) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_east, advanceAt225_east, advanceAt225_west, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, advanceAt234_east, advanceAt235_east, advanceAt236_east, advanceAt237_east, advanceAt238_east, advanceAt239_east, advanceAt240_east, advanceAt241_east, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt224_east, h224, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 225) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 225), d261985), oracleMember929, same, ?_⟩
      simp only [d261984, d261985, d0, d1, h224, h225, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h226 : p 226 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .east = some (.push 225 (.stay 226)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_east, advanceAt225_east, advanceAt225_west, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, advanceAt234_east, advanceAt235_east, advanceAt236_east, advanceAt237_east, advanceAt238_east, advanceAt239_east, advanceAt240_east, advanceAt241_east, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt224_east, h224, h225, h226, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 225 (.stay 226)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 225 (.stay 226)), d300100), oracleMember930, same, ?_⟩
        simp only [d216468, d300099, d300100, d0, d1, h224, h225, h226, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_east, advanceAt225_east, advanceAt225_west, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, advanceAt234_east, advanceAt235_east, advanceAt236_east, advanceAt237_east, advanceAt238_east, advanceAt239_east, advanceAt240_east, advanceAt241_east, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt224_east, h224, h225, h226, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_east, advanceAt225_east, advanceAt225_west, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, advanceAt234_east, advanceAt235_east, advanceAt236_east, advanceAt237_east, advanceAt238_east, advanceAt239_east, advanceAt240_east, advanceAt241_east, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt224_east, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover931 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .west = some outcome) :
    OracleCovered rowCases931 p outcome := by
  cases h224 : p 224 with
  | false =>
    cases h223 : p 223 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .west = some (.walk 223) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_west, advanceAt221_west, advanceAt222_west, advanceAt223_east, advanceAt223_west, advanceAt224_west, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_west, h223, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 223) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 223), d241830), oracleMember931, same, ?_⟩
      simp only [d202304, d241830, d0, d1, h223, h224, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_west, advanceAt221_west, advanceAt222_west, advanceAt223_east, advanceAt223_west, advanceAt224_west, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_west, h223, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_west, advanceAt221_west, advanceAt222_west, advanceAt223_east, advanceAt223_west, advanceAt224_west, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_west, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover932 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .northEast = some outcome) :
    OracleCovered rowCases932 p outcome := by
  cases h224 : p 224 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_north, advanceAt224_east, advanceAt224_northEast, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, cornerAt224_northEast, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_north, advanceAt224_east, advanceAt224_northEast, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, cornerAt224_northEast, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover933 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .northWest = some outcome) :
    OracleCovered rowCases933 p outcome := by
  cases h224 : p 224 with
  | false =>
    cases h202 : p 202 with
    | false =>
      cases h201 : p 201 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .northWest = some (.walk 201) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_north, advanceAt224_west, advanceAt224_northWest, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_northWest, h201, h202, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 201) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 201), d241832), oracleMember932, same, ?_⟩
        simp only [d202304, d241830, d241831, d241832, d0, d1, h201, h202, h224, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_north, advanceAt224_west, advanceAt224_northWest, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_northWest, h201, h202, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h223 : p 223 with
      | false =>
        cases h201 : p 201 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .northWest = some (.walk 201) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_north, advanceAt224_west, advanceAt224_northWest, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_northWest, h201, h202, h223, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 201) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 201), d241832), oracleMember932, same, ?_⟩
          simp only [d202304, d241830, d241831, d241832, d0, d1, h201, h202, h223, h224, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_north, advanceAt224_west, advanceAt224_northWest, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_northWest, h201, h202, h223, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_north, advanceAt224_west, advanceAt224_northWest, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_northWest, h202, h223, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_north, advanceAt224_west, advanceAt224_northWest, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, cornerAt224_northWest, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover934 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southEast = some outcome) :
    OracleCovered rowCases934 p outcome := by
  cases h224 : p 224 with
  | false =>
    cases h246 : p 246 with
    | false =>
      cases h247 : p 247 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southEast = some (.walk 247) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt224_east, advanceAt224_southEast, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt224_southEast, h224, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 247) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 247), d306035), oracleMember933, same, ?_⟩
        simp only [d271213, d271214, d306034, d306035, d0, d1, h224, h246, h247, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt224_east, advanceAt224_southEast, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt224_southEast, h224, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h225 : p 225 with
      | false =>
        cases h247 : p 247 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southEast = some (.walk 247) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt224_east, advanceAt224_southEast, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt224_southEast, h224, h225, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 247) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 247), d306035), oracleMember933, same, ?_⟩
          simp only [d271213, d271214, d306034, d306035, d0, d1, h224, h225, h246, h247, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt224_east, advanceAt224_southEast, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt224_southEast, h224, h225, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt224_east, advanceAt224_southEast, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt224_southEast, h224, h225, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt224_east, advanceAt224_southEast, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt224_southEast, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover935 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southWest = some outcome) :
    OracleCovered rowCases935 p outcome := by
  cases h224 : p 224 with
  | false =>
    cases h246 : p 246 with
    | false =>
      cases h245 : p 245 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southWest = some (.walk 245) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt224_west, advanceAt224_southWest, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt224_southWest, h224, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 245) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 245), d310057), oracleMember934, same, ?_⟩
        simp only [d202304, d253269, d287735, d310056, d310057, d0, d1, h224, h245, h246, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt224_west, advanceAt224_southWest, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt224_southWest, h224, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h223 : p 223 with
      | false =>
        cases h245 : p 245 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southWest = some (.walk 245) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt224_west, advanceAt224_southWest, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt224_southWest, h223, h224, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 245) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 245), d310057), oracleMember934, same, ?_⟩
          simp only [d202304, d253269, d287735, d310056, d310057, d0, d1, h223, h224, h245, h246, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt224_west, advanceAt224_southWest, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt224_southWest, h223, h224, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt224_west, advanceAt224_southWest, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt224_southWest, h223, h224, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt224_south, advanceAt224_west, advanceAt224_southWest, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt224_southWest, h224, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover936 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .north = some outcome) :
    OracleCovered rowCases936 p outcome := by
  cases h225 : p 225 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt27_north, advanceAt49_north, advanceAt71_north, advanceAt93_north, advanceAt115_north, advanceAt137_north, advanceAt159_north, advanceAt181_north, advanceAt203_north, advanceAt203_south, advanceAt225_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, cornerAt225_north, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt27_north, advanceAt49_north, advanceAt71_north, advanceAt93_north, advanceAt115_north, advanceAt137_north, advanceAt159_north, advanceAt181_north, advanceAt203_north, advanceAt203_south, advanceAt225_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, cornerAt225_north, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover937 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .south = some outcome) :
    OracleCovered rowCases937 p outcome := by
  cases h225 : p 225 with
  | false =>
    cases h247 : p 247 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .south = some (.walk 247) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt247_north, advanceAt247_south, advanceAt269_south, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt225_south, h225, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 247) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 247), d310774), oracleMember935, same, ?_⟩
      simp only [d271213, d310774, d0, d1, h225, h247, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt247_north, advanceAt247_south, advanceAt269_south, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt225_south, h225, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt247_north, advanceAt247_south, advanceAt269_south, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt225_south, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover938 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .east = some outcome) :
    OracleCovered rowCases938 p outcome := by
  cases h225 : p 225 with
  | false =>
    cases h226 : p 226 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .east = some (.walk 226) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_east, advanceAt226_east, advanceAt226_west, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, advanceAt234_east, advanceAt235_east, advanceAt236_east, advanceAt237_east, advanceAt238_east, advanceAt239_east, advanceAt240_east, advanceAt241_east, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt225_east, h225, h226, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 226) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 226), d277739), oracleMember936, same, ?_⟩
      simp only [d216468, d277739, d0, d1, h225, h226, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_east, advanceAt226_east, advanceAt226_west, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, advanceAt234_east, advanceAt235_east, advanceAt236_east, advanceAt237_east, advanceAt238_east, advanceAt239_east, advanceAt240_east, advanceAt241_east, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt225_east, h225, h226, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_east, advanceAt226_east, advanceAt226_west, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, advanceAt234_east, advanceAt235_east, advanceAt236_east, advanceAt237_east, advanceAt238_east, advanceAt239_east, advanceAt240_east, advanceAt241_east, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt225_east, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover939 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .west = some outcome) :
    OracleCovered rowCases939 p outcome := by
  cases h225 : p 225 with
  | false =>
    cases h224 : p 224 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .west = some (.walk 224) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_west, advanceAt221_west, advanceAt222_west, advanceAt223_west, advanceAt224_east, advanceAt224_west, advanceAt225_west, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, cornerAt225_west, h224, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 224) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 224), d261985), oracleMember937, same, ?_⟩
      simp only [d261984, d261985, d0, d1, h224, h225, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h223 : p 223 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .west = some (.push 224 (.stay 223)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_west, advanceAt221_west, advanceAt222_west, advanceAt223_west, advanceAt224_east, advanceAt224_west, advanceAt225_west, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, cornerAt225_west, h223, h224, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 224 (.stay 223)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 224 (.stay 223)), d282284), oracleMember938, same, ?_⟩
        simp only [d261984, d282283, d282284, d0, d1, h223, h224, h225, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_west, advanceAt221_west, advanceAt222_west, advanceAt223_west, advanceAt224_east, advanceAt224_west, advanceAt225_west, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, cornerAt225_west, h223, h224, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_west, advanceAt221_west, advanceAt222_west, advanceAt223_west, advanceAt224_east, advanceAt224_west, advanceAt225_west, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, cornerAt225_west, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover940 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .northEast = some outcome) :
    OracleCovered rowCases940 p outcome := by
  cases h225 : p 225 with
  | false =>
    cases h226 : p 226 with
    | false =>
      cases h204 : p 204 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .northEast = some (.walk 204) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_north, advanceAt225_east, advanceAt225_northEast, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, cornerAt225_northEast, h204, h225, h226, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 204) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 204), d277740), oracleMember939, same, ?_⟩
        simp only [d216468, d277739, d277740, d0, d1, h204, h225, h226, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_north, advanceAt225_east, advanceAt225_northEast, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, cornerAt225_northEast, h204, h225, h226, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_north, advanceAt225_east, advanceAt225_northEast, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, cornerAt225_northEast, h225, h226, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_north, advanceAt225_east, advanceAt225_northEast, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, cornerAt225_northEast, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover941 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .northWest = some outcome) :
    OracleCovered rowCases941 p outcome := by
  cases h225 : p 225 with
  | false =>
    cases h224 : p 224 with
    | false =>
      cases h202 : p 202 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .northWest = some (.walk 202) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_north, advanceAt225_west, advanceAt225_northWest, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, cornerAt225_northWest, h202, h224, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 202) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 202), d261986), oracleMember940, same, ?_⟩
        simp only [d261984, d261985, d261986, d0, d1, h202, h224, h225, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_north, advanceAt225_west, advanceAt225_northWest, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, cornerAt225_northWest, h202, h224, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_north, advanceAt225_west, advanceAt225_northWest, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, cornerAt225_northWest, h224, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_north, advanceAt225_west, advanceAt225_northWest, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, cornerAt225_northWest, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover942 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southEast = some outcome) :
    OracleCovered rowCases942 p outcome := by
  cases h225 : p 225 with
  | false =>
    cases h247 : p 247 with
    | false =>
      cases h248 : p 248 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southEast = some (.walk 248) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt225_east, advanceAt225_southEast, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt225_southEast, clearBoxAt248_249, clearBoxAt248_250, clearBoxAt248_251, clearBoxAt248_252, clearBoxAt248_253, clearBoxAt248_254, clearBoxAt248_255, clearBoxAt248_256, clearBoxAt248_257, clearBoxAt248_258, clearBoxAt248_259, clearBoxAt248_260, h225, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 248) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 248), d318725), oracleMember941, same, ?_⟩
        simp only [d13, d14, d318724, d318725, d0, d1, h225, h247, h248, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt225_east, advanceAt225_southEast, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt225_southEast, clearBoxAt248_249, clearBoxAt248_250, clearBoxAt248_251, clearBoxAt248_252, clearBoxAt248_253, clearBoxAt248_254, clearBoxAt248_255, clearBoxAt248_256, clearBoxAt248_257, clearBoxAt248_258, clearBoxAt248_259, clearBoxAt248_260, h225, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h226 : p 226 with
      | false =>
        cases h248 : p 248 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southEast = some (.walk 248) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt225_east, advanceAt225_southEast, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt225_southEast, clearBoxAt248_249, clearBoxAt248_250, clearBoxAt248_251, clearBoxAt248_252, clearBoxAt248_253, clearBoxAt248_254, clearBoxAt248_255, clearBoxAt248_256, clearBoxAt248_257, clearBoxAt248_258, clearBoxAt248_259, clearBoxAt248_260, h225, h226, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 248) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 248), d318725), oracleMember941, same, ?_⟩
          simp only [d13, d14, d318724, d318725, d0, d1, h225, h226, h247, h248, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt225_east, advanceAt225_southEast, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt225_southEast, clearBoxAt248_249, clearBoxAt248_250, clearBoxAt248_251, clearBoxAt248_252, clearBoxAt248_253, clearBoxAt248_254, clearBoxAt248_255, clearBoxAt248_256, clearBoxAt248_257, clearBoxAt248_258, clearBoxAt248_259, clearBoxAt248_260, h225, h226, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt225_east, advanceAt225_southEast, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt225_southEast, clearBoxAt248_249, clearBoxAt248_250, clearBoxAt248_251, clearBoxAt248_252, clearBoxAt248_253, clearBoxAt248_254, clearBoxAt248_255, clearBoxAt248_256, clearBoxAt248_257, clearBoxAt248_258, clearBoxAt248_259, clearBoxAt248_260, h225, h226, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt225_east, advanceAt225_southEast, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt225_southEast, clearBoxAt248_249, clearBoxAt248_250, clearBoxAt248_251, clearBoxAt248_252, clearBoxAt248_253, clearBoxAt248_254, clearBoxAt248_255, clearBoxAt248_256, clearBoxAt248_257, clearBoxAt248_258, clearBoxAt248_259, clearBoxAt248_260, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover943 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southWest = some outcome) :
    OracleCovered rowCases943 p outcome := by
  cases h225 : p 225 with
  | false =>
    cases h247 : p 247 with
    | false =>
      cases h246 : p 246 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southWest = some (.walk 246) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt225_west, advanceAt225_southWest, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt225_southWest, h225, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 246) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 246), d322255), oracleMember942, same, ?_⟩
        simp only [d253269, d271213, d271214, d271215, d322254, d322255, d0, d1, h225, h246, h247, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt225_west, advanceAt225_southWest, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt225_southWest, h225, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h224 : p 224 with
      | false =>
        cases h246 : p 246 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southWest = some (.walk 246) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt225_west, advanceAt225_southWest, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt225_southWest, h224, h225, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 246) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 246), d322255), oracleMember942, same, ?_⟩
          simp only [d253269, d271213, d271214, d271215, d322254, d322255, d0, d1, h224, h225, h246, h247, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt225_west, advanceAt225_southWest, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt225_southWest, h224, h225, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt225_west, advanceAt225_southWest, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt225_southWest, h224, h225, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt225_south, advanceAt225_west, advanceAt225_southWest, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt225_southWest, h225, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover944 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 226 .north = some outcome) :
    OracleCovered rowCases944 p outcome := by
  cases h226 : p 226 with
  | false =>
    cases h204 : p 204 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 226 .north = some (.walk 204) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt28_north, advanceAt50_north, advanceAt72_north, advanceAt94_north, advanceAt116_north, advanceAt138_north, advanceAt160_north, advanceAt182_north, advanceAt204_north, advanceAt204_south, advanceAt226_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, cornerAt226_north, h204, h226, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 204) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 204), d267844), oracleMember943, same, ?_⟩
      simp only [d216468, d267844, d0, d1, h204, h226, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h182 : p 182 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 226 .north = some (.push 204 (.stay 182)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt28_north, advanceAt50_north, advanceAt72_north, advanceAt94_north, advanceAt116_north, advanceAt138_north, advanceAt160_north, advanceAt182_north, advanceAt204_north, advanceAt204_south, advanceAt226_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, cornerAt226_north, h182, h204, h226, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 204 (.stay 182)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 204 (.stay 182)), d216471), oracleMember944, same, ?_⟩
        simp only [d216468, d216470, d216471, d0, d1, h182, h204, h226, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 226 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt28_north, advanceAt50_north, advanceAt72_north, advanceAt94_north, advanceAt116_north, advanceAt138_north, advanceAt160_north, advanceAt182_north, advanceAt204_north, advanceAt204_south, advanceAt226_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, cornerAt226_north, h182, h204, h226, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 226 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt28_north, advanceAt50_north, advanceAt72_north, advanceAt94_north, advanceAt116_north, advanceAt138_north, advanceAt160_north, advanceAt182_north, advanceAt204_north, advanceAt204_south, advanceAt226_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, cornerAt226_north, h226, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko22Hazard87
