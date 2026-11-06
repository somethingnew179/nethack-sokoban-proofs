import NetHack.Soko22Hazard87.OracleCover028Part4
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover1005 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 .northWest = some outcome) :
    OracleCovered rowCases1005 p outcome := by
  cases h250 : p 250 with
  | false =>
    cases h10250 : p 10250 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt250_north, advanceAt250_west, advanceAt250_northWest, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, cornerAt250_northWest, h250, h10250, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt250_north, advanceAt250_west, advanceAt250_northWest, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, cornerAt250_northWest, h250, h10250, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt250_north, advanceAt250_west, advanceAt250_northWest, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, cornerAt250_northWest, h250, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1006 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 .southEast = some outcome) :
    OracleCovered rowCases1006 p outcome := by
  cases h250 : p 250 with
  | false =>
    cases h10250 : p 10250 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt250_south, advanceAt250_east, advanceAt250_southEast, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt250_southEast, h250, h10250, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt250_south, advanceAt250_east, advanceAt250_southEast, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt250_southEast, h250, h10250, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt250_south, advanceAt250_east, advanceAt250_southEast, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt250_southEast, h250, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1007 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 .southWest = some outcome) :
    OracleCovered rowCases1007 p outcome := by
  cases h250 : p 250 with
  | false =>
    cases h10250 : p 10250 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt250_south, advanceAt250_west, advanceAt250_southWest, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt250_southWest, h250, h10250, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt250_south, advanceAt250_west, advanceAt250_southWest, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt250_southWest, h250, h10250, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt250_south, advanceAt250_west, advanceAt250_southWest, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt250_southWest, h250, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1008 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 .north = some outcome) :
    OracleCovered rowCases1008 p outcome := by
  cases h251 : p 251 with
  | false =>
    cases h10251 : p 10251 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt9_north, advanceAt31_north, advanceAt53_north, advanceAt75_north, advanceAt97_north, advanceAt119_north, advanceAt141_north, advanceAt163_north, advanceAt185_north, advanceAt207_north, advanceAt229_north, advanceAt229_south, advanceAt251_north, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, cornerAt251_north, h251, h10251, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt9_north, advanceAt31_north, advanceAt53_north, advanceAt75_north, advanceAt97_north, advanceAt119_north, advanceAt141_north, advanceAt163_north, advanceAt185_north, advanceAt207_north, advanceAt229_north, advanceAt229_south, advanceAt251_north, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, cornerAt251_north, h251, h10251, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt9_north, advanceAt31_north, advanceAt53_north, advanceAt75_north, advanceAt97_north, advanceAt119_north, advanceAt141_north, advanceAt163_north, advanceAt185_north, advanceAt207_north, advanceAt229_north, advanceAt229_south, advanceAt251_north, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, cornerAt251_north, h251, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1009 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 .south = some outcome) :
    OracleCovered rowCases1009 p outcome := by
  cases h251 : p 251 with
  | false =>
    cases h10251 : p 10251 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt251_south, advanceAt273_north, advanceAt273_south, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt251_south, h251, h10251, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt251_south, advanceAt273_north, advanceAt273_south, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt251_south, h251, h10251, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt251_south, advanceAt273_north, advanceAt273_south, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt251_south, h251, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko22Hazard87
