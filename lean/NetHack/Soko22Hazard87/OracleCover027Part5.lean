import NetHack.Soko22Hazard87.OracleCover027Part4
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover970 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .east = some outcome) :
    OracleCovered rowCases970 p outcome := by
  cases h246 : p 246 with
  | false =>
    cases h247 : p 247 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .east = some (.walk 247) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_east, advanceAt247_east, advanceAt247_west, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt246_east, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 247) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 247), d271214), oracleMember959, same, ?_⟩
      simp only [d271213, d271214, d0, d1, h246, h247, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h248 : p 248 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .east = some (.push 247 (.stay 248)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_east, advanceAt247_east, advanceAt247_west, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt246_east, h246, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 247 (.stay 248)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 247 (.stay 248)), d46864), oracleMember960, same, ?_⟩
        simp only [d13, d44880, d46864, d0, d1, h246, h247, h248, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_east, advanceAt247_east, advanceAt247_west, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt246_east, h246, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_east, advanceAt247_east, advanceAt247_west, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt246_east, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover971 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .west = some outcome) :
    OracleCovered rowCases971 p outcome := by
  cases h246 : p 246 with
  | false =>
    cases h245 : p 245 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .west = some (.walk 245) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_east, advanceAt245_west, advanceAt246_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_west, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 245) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 245), d338547), oracleMember961, same, ?_⟩
      simp only [d253269, d338547, d0, d1, h245, h246, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_east, advanceAt245_west, advanceAt246_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_west, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_east, advanceAt245_west, advanceAt246_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_west, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover972 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northEast = some outcome) :
    OracleCovered rowCases972 p outcome := by
  cases h246 : p 246 with
  | false =>
    cases h224 : p 224 with
    | false =>
      cases h225 : p 225 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northEast = some (.walk 225) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_north, advanceAt246_east, advanceAt246_northEast, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt246_northEast, h224, h225, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 225) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 225), d322255), oracleMember962, same, ?_⟩
        simp only [d253269, d271213, d271214, d271215, d322254, d322255, d0, d1, h224, h225, h246, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_north, advanceAt246_east, advanceAt246_northEast, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt246_northEast, h224, h225, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h247 : p 247 with
      | false =>
        cases h225 : p 225 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northEast = some (.walk 225) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_north, advanceAt246_east, advanceAt246_northEast, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt246_northEast, h224, h225, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 225) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 225), d322255), oracleMember962, same, ?_⟩
          simp only [d253269, d271213, d271214, d271215, d322254, d322255, d0, d1, h224, h225, h246, h247, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_north, advanceAt246_east, advanceAt246_northEast, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt246_northEast, h224, h225, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_north, advanceAt246_east, advanceAt246_northEast, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt246_northEast, h224, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_north, advanceAt246_east, advanceAt246_northEast, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt246_northEast, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover973 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northWest = some outcome) :
    OracleCovered rowCases973 p outcome := by
  cases h246 : p 246 with
  | false =>
    cases h224 : p 224 with
    | false =>
      cases h223 : p 223 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northWest = some (.walk 223) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_north, advanceAt246_west, advanceAt246_northWest, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_northWest, h223, h224, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 223) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 223), d287737), oracleMember963, same, ?_⟩
        simp only [d253269, d287734, d287735, d287736, d287737, d0, d1, h223, h224, h246, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_north, advanceAt246_west, advanceAt246_northWest, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_northWest, h223, h224, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h245 : p 245 with
      | false =>
        cases h223 : p 223 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northWest = some (.walk 223) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_north, advanceAt246_west, advanceAt246_northWest, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_northWest, h223, h224, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 223) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 223), d287737), oracleMember963, same, ?_⟩
          simp only [d253269, d287734, d287735, d287736, d287737, d0, d1, h223, h224, h245, h246, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_north, advanceAt246_west, advanceAt246_northWest, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_northWest, h223, h224, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_north, advanceAt246_west, advanceAt246_northWest, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_northWest, h224, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_north, advanceAt246_west, advanceAt246_northWest, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt246_northWest, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover974 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .southEast = some outcome) :
    OracleCovered rowCases974 p outcome := by
  cases h246 : p 246 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_south, advanceAt246_east, advanceAt246_southEast, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt246_southEast, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt246_south, advanceAt246_east, advanceAt246_southEast, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt246_southEast, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko22Hazard87
