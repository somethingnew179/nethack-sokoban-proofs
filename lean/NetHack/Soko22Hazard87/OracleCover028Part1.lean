import NetHack.Soko22Hazard87.OracleCover028Part0
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover985 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .south = some outcome) :
    OracleCovered rowCases985 p outcome := by
  cases h248 : p 248 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_south, advanceAt270_north, advanceAt270_south, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt248_south, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_south, advanceAt270_north, advanceAt270_south, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt248_south, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover986 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .east = some outcome) :
    OracleCovered rowCases986 p outcome := by
  cases h248 : p 248 with
  | false =>
    cases h249 : p 249 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .east = some (.walk 249) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_east, advanceAt249_east, advanceAt249_west, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt248_east, h248, h249, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 249) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 249), d370801), oracleMember983, same, ?_⟩
      simp only [d13, d370801, d0, d1, h248, h249, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h250 : p 250 with
      | false =>
        cases h10250 : p 10250 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .east = some (.push 249 (.stay 250)) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_east, advanceAt249_east, advanceAt249_west, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt248_east, h248, h249, h250, h10250, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.push 249 (.stay 250)) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.push 249 (.stay 250)), d370936), oracleMember985, same, ?_⟩
          simp only [d13, d370934, d370935, d370936, d0, d1, h248, h249, h250, h10250, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .east = some (.push 249 (.fill 250)) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_east, advanceAt249_east, advanceAt249_west, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt248_east, h248, h249, h250, h10250, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.push 249 (.fill 250)) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.push 249 (.fill 250)), d370807), oracleMember984, same, ?_⟩
          simp only [d13, d370805, d370806, d370807, d0, d1, h248, h249, h250, h10250, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_east, advanceAt249_east, advanceAt249_west, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt248_east, h248, h249, h250, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_east, advanceAt249_east, advanceAt249_west, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt248_east, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover987 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .west = some outcome) :
    OracleCovered rowCases987 p outcome := by
  cases h248 : p 248 with
  | false =>
    cases h247 : p 247 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .west = some (.walk 247) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_east, advanceAt247_west, advanceAt248_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_west, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 247) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 247), d14), oracleMember986, same, ?_⟩
      simp only [d13, d14, d0, d1, h247, h248, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h246 : p 246 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .west = some (.push 247 (.stay 246)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_east, advanceAt247_west, advanceAt248_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_west, h246, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 247 (.stay 246)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 247 (.stay 246)), d46864), oracleMember987, same, ?_⟩
        simp only [d13, d44880, d46864, d0, d1, h246, h247, h248, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_east, advanceAt247_west, advanceAt248_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_west, h246, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_east, advanceAt247_west, advanceAt248_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_west, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover988 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .northEast = some outcome) :
    OracleCovered rowCases988 p outcome := by
  cases h248 : p 248 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_north, advanceAt248_east, advanceAt248_northEast, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, cornerAt248_northEast, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_north, advanceAt248_east, advanceAt248_northEast, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, cornerAt248_northEast, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover989 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .northWest = some outcome) :
    OracleCovered rowCases989 p outcome := by
  cases h248 : p 248 with
  | false =>
    cases h226 : p 226 with
    | false =>
      cases h225 : p 225 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .northWest = some (.walk 225) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_north, advanceAt248_west, advanceAt248_northWest, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_northWest, h225, h226, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 225) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 225), d318725), oracleMember988, same, ?_⟩
        simp only [d13, d14, d318724, d318725, d0, d1, h225, h226, h248, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_north, advanceAt248_west, advanceAt248_northWest, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_northWest, h225, h226, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h247 : p 247 with
      | false =>
        cases h225 : p 225 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .northWest = some (.walk 225) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_north, advanceAt248_west, advanceAt248_northWest, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_northWest, h225, h226, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 225) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 225), d318725), oracleMember988, same, ?_⟩
          simp only [d13, d14, d318724, d318725, d0, d1, h225, h226, h247, h248, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_north, advanceAt248_west, advanceAt248_northWest, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_northWest, h225, h226, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_north, advanceAt248_west, advanceAt248_northWest, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_northWest, h226, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt248_north, advanceAt248_west, advanceAt248_northWest, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_northWest, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko22Hazard87
