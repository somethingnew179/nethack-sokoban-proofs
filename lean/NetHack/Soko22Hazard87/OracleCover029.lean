import NetHack.Soko22Hazard87.OracleCover028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover1015 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 .southWest = some outcome) :
    OracleCovered rowCases1015 p outcome := by
  cases h251 : p 251 with
  | false =>
    cases h10251 : p 10251 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt251_south, advanceAt251_west, advanceAt251_southWest, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt251_southWest, h251, h10251, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt251_south, advanceAt251_west, advanceAt251_southWest, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt251_southWest, h251, h10251, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt251_south, advanceAt251_west, advanceAt251_southWest, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt251_southWest, h251, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1016 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .north = some outcome) :
    OracleCovered rowCases1016 p outcome := by
  cases h252 : p 252 with
  | false =>
    cases h10252 : p 10252 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt32_north, advanceAt54_north, advanceAt76_north, advanceAt98_north, advanceAt120_north, advanceAt142_north, advanceAt164_north, advanceAt186_north, advanceAt208_north, advanceAt230_north, advanceAt230_south, advanceAt252_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_north, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt32_north, advanceAt54_north, advanceAt76_north, advanceAt98_north, advanceAt120_north, advanceAt142_north, advanceAt164_north, advanceAt186_north, advanceAt208_north, advanceAt230_north, advanceAt230_south, advanceAt252_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_north, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt32_north, advanceAt54_north, advanceAt76_north, advanceAt98_north, advanceAt120_north, advanceAt142_north, advanceAt164_north, advanceAt186_north, advanceAt208_north, advanceAt230_north, advanceAt230_south, advanceAt252_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_north, h252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1017 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .south = some outcome) :
    OracleCovered rowCases1017 p outcome := by
  cases h252 : p 252 with
  | false =>
    cases h10252 : p 10252 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_south, advanceAt274_north, advanceAt274_south, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt252_south, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_south, advanceAt274_north, advanceAt274_south, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt252_south, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_south, advanceAt274_north, advanceAt274_south, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt252_south, h252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1018 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .east = some outcome) :
    OracleCovered rowCases1018 p outcome := by
  cases h252 : p 252 with
  | false =>
    cases h10252 : p 10252 with
    | false =>
      cases h253 : p 253 with
      | false =>
        cases h10253 : p 10253 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .east = some (.walk 253) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_east, advanceAt253_east, advanceAt253_west, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt252_east, h252, h253, h10252, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 253) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 253), d379583), oracleMember1005, same, ?_⟩
          simp only [d364936, d379581, d379582, d379583, d0, d1, h252, h253, h10252, h10253, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .east = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_east, advanceAt253_east, advanceAt253_west, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt252_east, h252, h253, h10252, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        cases h254 : p 254 with
        | false =>
          cases h10254 : p 10254 with
          | false =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .east = some (.push 253 (.stay 254)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_east, advanceAt253_east, advanceAt253_west, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt252_east, h252, h253, h254, h10252, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 253 (.stay 254)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 253 (.stay 254)), d379875), oracleMember1007, same, ?_⟩
            simp only [d365414, d379872, d379873, d379874, d379875, d0, d1, h252, h253, h254, h10252, h10254, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
          | true =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .east = some (.push 253 (.fill 254)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_east, advanceAt253_east, advanceAt253_west, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt252_east, h252, h253, h254, h10252, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 253 (.fill 254)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 253 (.fill 254)), d379733), oracleMember1006, same, ?_⟩
            simp only [d364954, d379730, d379731, d379732, d379733, d0, d1, h252, h253, h254, h10252, h10254, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .east = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_east, advanceAt253_east, advanceAt253_west, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt252_east, h252, h253, h254, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_east, advanceAt253_east, advanceAt253_west, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt252_east, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_east, advanceAt253_east, advanceAt253_west, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt252_east, h252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1019 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .west = some outcome) :
    OracleCovered rowCases1019 p outcome := by
  cases h252 : p 252 with
  | false =>
    cases h10252 : p 10252 with
    | false =>
      cases h251 : p 251 with
      | false =>
        cases h10251 : p 10251 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .west = some (.walk 251) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_east, advanceAt251_west, advanceAt252_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_west, h251, h252, h10251, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 251) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 251), d379277), oracleMember1008, same, ?_⟩
          simp only [d364397, d379275, d379276, d379277, d0, d1, h251, h252, h10251, h10252, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .west = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_east, advanceAt251_west, advanceAt252_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_west, h251, h252, h10251, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        cases h250 : p 250 with
        | false =>
          cases h10250 : p 10250 with
          | false =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .west = some (.push 251 (.stay 250)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_east, advanceAt251_west, advanceAt252_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_west, h250, h251, h252, h10250, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 251 (.stay 250)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 251 (.stay 250)), d379271), oracleMember1010, same, ?_⟩
            simp only [d364397, d379268, d379269, d379270, d379271, d0, d1, h250, h251, h252, h10250, h10252, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
          | true =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .west = some (.push 251 (.fill 250)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_east, advanceAt251_west, advanceAt252_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_west, h250, h251, h252, h10250, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 251 (.fill 250)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 251 (.fill 250)), d379882), oracleMember1009, same, ?_⟩
            simp only [d364397, d379879, d379880, d379881, d379882, d0, d1, h250, h251, h252, h10250, h10252, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .west = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_east, advanceAt251_west, advanceAt252_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_west, h250, h251, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_east, advanceAt251_west, advanceAt252_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_west, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_east, advanceAt251_west, advanceAt252_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_west, h252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1020 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .northEast = some outcome) :
    OracleCovered rowCases1020 p outcome := by
  cases h252 : p 252 with
  | false =>
    cases h10252 : p 10252 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_north, advanceAt252_east, advanceAt252_northEast, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt252_northEast, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_north, advanceAt252_east, advanceAt252_northEast, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt252_northEast, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_north, advanceAt252_east, advanceAt252_northEast, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt252_northEast, h252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1021 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .northWest = some outcome) :
    OracleCovered rowCases1021 p outcome := by
  cases h252 : p 252 with
  | false =>
    cases h10252 : p 10252 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_north, advanceAt252_west, advanceAt252_northWest, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_northWest, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_north, advanceAt252_west, advanceAt252_northWest, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_northWest, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_north, advanceAt252_west, advanceAt252_northWest, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, cornerAt252_northWest, h252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1022 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .southEast = some outcome) :
    OracleCovered rowCases1022 p outcome := by
  cases h252 : p 252 with
  | false =>
    cases h10252 : p 10252 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_south, advanceAt252_east, advanceAt252_southEast, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, cornerAt252_southEast, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_south, advanceAt252_east, advanceAt252_southEast, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, cornerAt252_southEast, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_south, advanceAt252_east, advanceAt252_southEast, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, cornerAt252_southEast, h252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1023 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .southWest = some outcome) :
    OracleCovered rowCases1023 p outcome := by
  cases h252 : p 252 with
  | false =>
    cases h10252 : p 10252 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_south, advanceAt252_west, advanceAt252_southWest, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt252_southWest, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_south, advanceAt252_west, advanceAt252_southWest, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt252_southWest, h252, h10252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt252_south, advanceAt252_west, advanceAt252_southWest, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt252_southWest, h252, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1024 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .north = some outcome) :
    OracleCovered rowCases1024 p outcome := by
  cases h253 : p 253 with
  | false =>
    cases h10253 : p 10253 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt33_north, advanceAt55_north, advanceAt77_north, advanceAt99_north, advanceAt121_north, advanceAt143_north, advanceAt165_north, advanceAt187_north, advanceAt209_north, advanceAt231_north, advanceAt231_south, advanceAt253_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_north, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt33_north, advanceAt55_north, advanceAt77_north, advanceAt99_north, advanceAt121_north, advanceAt143_north, advanceAt165_north, advanceAt187_north, advanceAt209_north, advanceAt231_north, advanceAt231_south, advanceAt253_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_north, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt33_north, advanceAt55_north, advanceAt77_north, advanceAt99_north, advanceAt121_north, advanceAt143_north, advanceAt165_north, advanceAt187_north, advanceAt209_north, advanceAt231_north, advanceAt231_south, advanceAt253_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_north, h253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1025 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .south = some outcome) :
    OracleCovered rowCases1025 p outcome := by
  cases h253 : p 253 with
  | false =>
    cases h10253 : p 10253 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_south, advanceAt275_north, advanceAt275_south, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, cornerAt253_south, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_south, advanceAt275_north, advanceAt275_south, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, cornerAt253_south, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_south, advanceAt275_north, advanceAt275_south, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, cornerAt253_south, h253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1026 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .east = some outcome) :
    OracleCovered rowCases1026 p outcome := by
  cases h253 : p 253 with
  | false =>
    cases h10253 : p 10253 with
    | false =>
      cases h254 : p 254 with
      | false =>
        cases h10254 : p 10254 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .east = some (.walk 254) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_east, advanceAt254_east, advanceAt254_west, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt253_east, h253, h254, h10253, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 254) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 254), d380014), oracleMember1011, same, ?_⟩
          simp only [d365414, d380012, d380013, d380014, d0, d1, h253, h254, h10253, h10254, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .east = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_east, advanceAt254_east, advanceAt254_west, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt253_east, h253, h254, h10253, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        cases h255 : p 255 with
        | false =>
          cases h10255 : p 10255 with
          | false =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .east = some (.push 254 (.stay 255)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_east, advanceAt254_east, advanceAt254_west, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt253_east, h253, h254, h255, h10253, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 254 (.stay 255)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 254 (.stay 255)), d380312), oracleMember1013, same, ?_⟩
            simp only [d365770, d380309, d380310, d380311, d380312, d0, d1, h253, h254, h255, h10253, h10255, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
          | true =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .east = some (.push 254 (.fill 255)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_east, advanceAt254_east, advanceAt254_west, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt253_east, h253, h254, h255, h10253, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 254 (.fill 255)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 254 (.fill 255)), d380167), oracleMember1012, same, ?_⟩
            simp only [d365435, d380164, d380165, d380166, d380167, d0, d1, h253, h254, h255, h10253, h10255, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .east = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_east, advanceAt254_east, advanceAt254_west, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt253_east, h253, h254, h255, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_east, advanceAt254_east, advanceAt254_west, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt253_east, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_east, advanceAt254_east, advanceAt254_west, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt253_east, h253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1027 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .west = some outcome) :
    OracleCovered rowCases1027 p outcome := by
  cases h253 : p 253 with
  | false =>
    cases h10253 : p 10253 with
    | false =>
      cases h252 : p 252 with
      | false =>
        cases h10252 : p 10252 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .west = some (.walk 252) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_east, advanceAt252_west, advanceAt253_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_west, h252, h253, h10252, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 252) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 252), d379583), oracleMember1014, same, ?_⟩
          simp only [d364936, d379581, d379582, d379583, d0, d1, h252, h253, h10252, h10253, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .west = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_east, advanceAt252_west, advanceAt253_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_west, h252, h253, h10252, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        cases h251 : p 251 with
        | false =>
          cases h10251 : p 10251 with
          | false =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .west = some (.push 252 (.stay 251)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_east, advanceAt252_west, advanceAt253_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_west, h251, h252, h253, h10251, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 252 (.stay 251)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 252 (.stay 251)), d379563), oracleMember1016, same, ?_⟩
            simp only [d364936, d379560, d379561, d379562, d379563, d0, d1, h251, h252, h253, h10251, h10253, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
          | true =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .west = some (.push 252 (.fill 251)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_east, advanceAt252_west, advanceAt253_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_west, h251, h252, h253, h10251, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 252 (.fill 251)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 252 (.fill 251)), d380319), oracleMember1015, same, ?_⟩
            simp only [d364936, d380316, d380317, d380318, d380319, d0, d1, h251, h252, h253, h10251, h10253, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .west = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_east, advanceAt252_west, advanceAt253_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_west, h251, h252, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_east, advanceAt252_west, advanceAt253_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_west, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_east, advanceAt252_west, advanceAt253_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_west, h253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1028 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .northEast = some outcome) :
    OracleCovered rowCases1028 p outcome := by
  cases h253 : p 253 with
  | false =>
    cases h10253 : p 10253 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_north, advanceAt253_east, advanceAt253_northEast, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt253_northEast, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_north, advanceAt253_east, advanceAt253_northEast, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt253_northEast, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_north, advanceAt253_east, advanceAt253_northEast, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt253_northEast, h253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1029 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .northWest = some outcome) :
    OracleCovered rowCases1029 p outcome := by
  cases h253 : p 253 with
  | false =>
    cases h10253 : p 10253 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_north, advanceAt253_west, advanceAt253_northWest, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_northWest, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_north, advanceAt253_west, advanceAt253_northWest, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_northWest, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_north, advanceAt253_west, advanceAt253_northWest, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, cornerAt253_northWest, h253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1030 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .southEast = some outcome) :
    OracleCovered rowCases1030 p outcome := by
  cases h253 : p 253 with
  | false =>
    cases h10253 : p 10253 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_south, advanceAt253_east, advanceAt253_southEast, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, cornerAt253_southEast, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_south, advanceAt253_east, advanceAt253_southEast, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, cornerAt253_southEast, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_south, advanceAt253_east, advanceAt253_southEast, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, cornerAt253_southEast, h253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1031 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .southWest = some outcome) :
    OracleCovered rowCases1031 p outcome := by
  cases h253 : p 253 with
  | false =>
    cases h10253 : p 10253 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_south, advanceAt253_west, advanceAt253_southWest, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, cornerAt253_southWest, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_south, advanceAt253_west, advanceAt253_southWest, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, cornerAt253_southWest, h253, h10253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt253_south, advanceAt253_west, advanceAt253_southWest, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, cornerAt253_southWest, h253, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1032 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .north = some outcome) :
    OracleCovered rowCases1032 p outcome := by
  cases h254 : p 254 with
  | false =>
    cases h10254 : p 10254 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt34_north, advanceAt56_north, advanceAt78_north, advanceAt100_north, advanceAt122_north, advanceAt144_north, advanceAt166_north, advanceAt188_north, advanceAt210_north, advanceAt232_north, advanceAt232_south, advanceAt254_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_north, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt34_north, advanceAt56_north, advanceAt78_north, advanceAt100_north, advanceAt122_north, advanceAt144_north, advanceAt166_north, advanceAt188_north, advanceAt210_north, advanceAt232_north, advanceAt232_south, advanceAt254_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_north, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt34_north, advanceAt56_north, advanceAt78_north, advanceAt100_north, advanceAt122_north, advanceAt144_north, advanceAt166_north, advanceAt188_north, advanceAt210_north, advanceAt232_north, advanceAt232_south, advanceAt254_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_north, h254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1033 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .south = some outcome) :
    OracleCovered rowCases1033 p outcome := by
  cases h254 : p 254 with
  | false =>
    cases h10254 : p 10254 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_south, advanceAt276_north, advanceAt276_south, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, cornerAt254_south, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_south, advanceAt276_north, advanceAt276_south, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, cornerAt254_south, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_south, advanceAt276_north, advanceAt276_south, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, cornerAt254_south, h254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1034 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .east = some outcome) :
    OracleCovered rowCases1034 p outcome := by
  cases h254 : p 254 with
  | false =>
    cases h10254 : p 10254 with
    | false =>
      cases h255 : p 255 with
      | false =>
        cases h10255 : p 10255 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .east = some (.walk 255) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_east, advanceAt255_east, advanceAt255_west, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt254_east, h254, h255, h10254, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 255) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 255), d380454), oracleMember1017, same, ?_⟩
          simp only [d365770, d380452, d380453, d380454, d0, d1, h254, h255, h10254, h10255, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .east = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_east, advanceAt255_east, advanceAt255_west, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt254_east, h254, h255, h10254, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        cases h256 : p 256 with
        | false =>
          cases h10256 : p 10256 with
          | false =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .east = some (.push 255 (.stay 256)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_east, advanceAt255_east, advanceAt255_west, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt254_east, h254, h255, h256, h10254, h10256, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 255 (.stay 256)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 255 (.stay 256)), d380710), oracleMember1019, same, ?_⟩
            simp only [d365990, d380707, d380708, d380709, d380710, d0, d1, h254, h255, h256, h10254, h10256, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
          | true =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .east = some (.push 255 (.fill 256)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_east, advanceAt255_east, advanceAt255_west, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt254_east, h254, h255, h256, h10254, h10256, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 255 (.fill 256)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 255 (.fill 256)), d380610), oracleMember1018, same, ?_⟩
            simp only [d365794, d380607, d380608, d380609, d380610, d0, d1, h254, h255, h256, h10254, h10256, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .east = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_east, advanceAt255_east, advanceAt255_west, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt254_east, h254, h255, h256, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_east, advanceAt255_east, advanceAt255_west, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt254_east, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_east, advanceAt255_east, advanceAt255_west, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt254_east, h254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1035 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .west = some outcome) :
    OracleCovered rowCases1035 p outcome := by
  cases h254 : p 254 with
  | false =>
    cases h10254 : p 10254 with
    | false =>
      cases h253 : p 253 with
      | false =>
        cases h10253 : p 10253 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .west = some (.walk 253) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_east, advanceAt253_west, advanceAt254_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_west, h253, h254, h10253, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 253) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 253), d380014), oracleMember1020, same, ?_⟩
          simp only [d365414, d380012, d380013, d380014, d0, d1, h253, h254, h10253, h10254, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .west = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_east, advanceAt253_west, advanceAt254_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_west, h253, h254, h10253, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        cases h252 : p 252 with
        | false =>
          cases h10252 : p 10252 with
          | false =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .west = some (.push 253 (.stay 252)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_east, advanceAt253_west, advanceAt254_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_west, h252, h253, h254, h10252, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 253 (.stay 252)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 253 (.stay 252)), d379875), oracleMember1022, same, ?_⟩
            simp only [d365414, d379872, d379873, d379874, d379875, d0, d1, h252, h253, h254, h10252, h10254, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
          | true =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .west = some (.push 253 (.fill 252)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_east, advanceAt253_west, advanceAt254_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_west, h252, h253, h254, h10252, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 253 (.fill 252)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 253 (.fill 252)), d380717), oracleMember1021, same, ?_⟩
            simp only [d365414, d380714, d380715, d380716, d380717, d0, d1, h252, h253, h254, h10252, h10254, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .west = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_east, advanceAt253_west, advanceAt254_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_west, h252, h253, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_east, advanceAt253_west, advanceAt254_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_west, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_east, advanceAt253_west, advanceAt254_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_west, h254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1036 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .northEast = some outcome) :
    OracleCovered rowCases1036 p outcome := by
  cases h254 : p 254 with
  | false =>
    cases h10254 : p 10254 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_north, advanceAt254_east, advanceAt254_northEast, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt254_northEast, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_north, advanceAt254_east, advanceAt254_northEast, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt254_northEast, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_north, advanceAt254_east, advanceAt254_northEast, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt254_northEast, h254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1037 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .northWest = some outcome) :
    OracleCovered rowCases1037 p outcome := by
  cases h254 : p 254 with
  | false =>
    cases h10254 : p 10254 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_north, advanceAt254_west, advanceAt254_northWest, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_northWest, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_north, advanceAt254_west, advanceAt254_northWest, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_northWest, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_north, advanceAt254_west, advanceAt254_northWest, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, cornerAt254_northWest, h254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1038 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .southEast = some outcome) :
    OracleCovered rowCases1038 p outcome := by
  cases h254 : p 254 with
  | false =>
    cases h10254 : p 10254 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_south, advanceAt254_east, advanceAt254_southEast, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, cornerAt254_southEast, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_south, advanceAt254_east, advanceAt254_southEast, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, cornerAt254_southEast, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_south, advanceAt254_east, advanceAt254_southEast, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, cornerAt254_southEast, h254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1039 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .southWest = some outcome) :
    OracleCovered rowCases1039 p outcome := by
  cases h254 : p 254 with
  | false =>
    cases h10254 : p 10254 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_south, advanceAt254_west, advanceAt254_southWest, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, cornerAt254_southWest, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_south, advanceAt254_west, advanceAt254_southWest, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, cornerAt254_southWest, h254, h10254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt254_south, advanceAt254_west, advanceAt254_southWest, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, cornerAt254_southWest, h254, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1040 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .north = some outcome) :
    OracleCovered rowCases1040 p outcome := by
  cases h255 : p 255 with
  | false =>
    cases h10255 : p 10255 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt13_north, advanceAt35_north, advanceAt57_north, advanceAt79_north, advanceAt101_north, advanceAt123_north, advanceAt145_north, advanceAt167_north, advanceAt189_north, advanceAt211_north, advanceAt233_north, advanceAt233_south, advanceAt255_north, floorAt13, doorAt13, trapAt13, boxAt13, holeAt13, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_north, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt13_north, advanceAt35_north, advanceAt57_north, advanceAt79_north, advanceAt101_north, advanceAt123_north, advanceAt145_north, advanceAt167_north, advanceAt189_north, advanceAt211_north, advanceAt233_north, advanceAt233_south, advanceAt255_north, floorAt13, doorAt13, trapAt13, boxAt13, holeAt13, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_north, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt13_north, advanceAt35_north, advanceAt57_north, advanceAt79_north, advanceAt101_north, advanceAt123_north, advanceAt145_north, advanceAt167_north, advanceAt189_north, advanceAt211_north, advanceAt233_north, advanceAt233_south, advanceAt255_north, floorAt13, doorAt13, trapAt13, boxAt13, holeAt13, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_north, h255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1041 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .south = some outcome) :
    OracleCovered rowCases1041 p outcome := by
  cases h255 : p 255 with
  | false =>
    cases h10255 : p 10255 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_south, advanceAt277_north, advanceAt277_south, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, cornerAt255_south, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_south, advanceAt277_north, advanceAt277_south, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, cornerAt255_south, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_south, advanceAt277_north, advanceAt277_south, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, cornerAt255_south, h255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1042 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .east = some outcome) :
    OracleCovered rowCases1042 p outcome := by
  cases h255 : p 255 with
  | false =>
    cases h10255 : p 10255 with
    | false =>
      cases h256 : p 256 with
      | false =>
        cases h10256 : p 10256 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .east = some (.walk 256) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_east, advanceAt256_east, advanceAt256_west, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt255_east, h255, h256, h10255, h10256, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 256) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 256), d380855), oracleMember1023, same, ?_⟩
          simp only [d365990, d380853, d380854, d380855, d0, d1, h255, h256, h10255, h10256, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .east = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_east, advanceAt256_east, advanceAt256_west, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt255_east, h255, h256, h10255, h10256, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        cases h257 : p 257 with
        | false =>
          cases h10257 : p 10257 with
          | false =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .east = some (.push 256 (.stay 257)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_east, advanceAt256_east, advanceAt256_west, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt255_east, h255, h256, h257, h10255, h10257, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 256 (.stay 257)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 256 (.stay 257)), d380918), oracleMember1025, same, ?_⟩
            simp only [d366035, d380915, d380916, d380917, d380918, d0, d1, h255, h256, h257, h10255, h10257, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
          | true =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .east = some (.push 256 (.fill 257)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_east, advanceAt256_east, advanceAt256_west, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt255_east, h255, h256, h257, h10255, h10257, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 256 (.fill 257)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 256 (.fill 257)), d380914), oracleMember1024, same, ?_⟩
            simp only [d366017, d380911, d380912, d380913, d380914, d0, d1, h255, h256, h257, h10255, h10257, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .east = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_east, advanceAt256_east, advanceAt256_west, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt255_east, h255, h256, h257, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_east, advanceAt256_east, advanceAt256_west, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt255_east, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_east, advanceAt256_east, advanceAt256_west, advanceAt257_east, advanceAt258_east, advanceAt259_east, advanceAt260_east, advanceAt261_east, advanceAt262_east, advanceAt263_east, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt255_east, h255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1043 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .west = some outcome) :
    OracleCovered rowCases1043 p outcome := by
  cases h255 : p 255 with
  | false =>
    cases h10255 : p 10255 with
    | false =>
      cases h254 : p 254 with
      | false =>
        cases h10254 : p 10254 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .west = some (.walk 254) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_west, advanceAt254_east, advanceAt254_west, advanceAt255_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_west, h254, h255, h10254, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 254) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 254), d380454), oracleMember1026, same, ?_⟩
          simp only [d365770, d380452, d380453, d380454, d0, d1, h254, h255, h10254, h10255, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .west = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_west, advanceAt254_east, advanceAt254_west, advanceAt255_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_west, h254, h255, h10254, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        cases h253 : p 253 with
        | false =>
          cases h10253 : p 10253 with
          | false =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .west = some (.push 254 (.stay 253)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_west, advanceAt254_east, advanceAt254_west, advanceAt255_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_west, h253, h254, h255, h10253, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 254 (.stay 253)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 254 (.stay 253)), d380312), oracleMember1028, same, ?_⟩
            simp only [d365770, d380309, d380310, d380311, d380312, d0, d1, h253, h254, h255, h10253, h10255, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
          | true =>
            have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .west = some (.push 254 (.fill 253)) := by
              simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_west, advanceAt254_east, advanceAt254_west, advanceAt255_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_west, h253, h254, h255, h10253, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
            have same : outcome = (.push 254 (.fill 253)) := Option.some.inj (checked.symm.trans evaluated)
            refine ⟨((.push 254 (.fill 253)), d380925), oracleMember1027, same, ?_⟩
            simp only [d365770, d380922, d380923, d380924, d380925, d0, d1, h253, h254, h255, h10253, h10255, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .west = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_west, advanceAt254_east, advanceAt254_west, advanceAt255_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_west, h253, h254, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_west, advanceAt254_east, advanceAt254_west, advanceAt255_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_west, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_west, advanceAt243_west, advanceAt244_west, advanceAt245_west, advanceAt246_west, advanceAt247_west, advanceAt248_west, advanceAt249_west, advanceAt250_west, advanceAt251_west, advanceAt252_west, advanceAt253_west, advanceAt254_east, advanceAt254_west, advanceAt255_west, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_west, h255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1044 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .northEast = some outcome) :
    OracleCovered rowCases1044 p outcome := by
  cases h255 : p 255 with
  | false =>
    cases h10255 : p 10255 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_north, advanceAt255_east, advanceAt255_northEast, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, cornerAt255_northEast, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_north, advanceAt255_east, advanceAt255_northEast, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, cornerAt255_northEast, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_north, advanceAt255_east, advanceAt255_northEast, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, cornerAt255_northEast, h255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1045 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .northWest = some outcome) :
    OracleCovered rowCases1045 p outcome := by
  cases h255 : p 255 with
  | false =>
    cases h10255 : p 10255 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_north, advanceAt255_west, advanceAt255_northWest, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_northWest, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_north, advanceAt255_west, advanceAt255_northWest, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_northWest, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_north, advanceAt255_west, advanceAt255_northWest, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, cornerAt255_northWest, h255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1046 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .southEast = some outcome) :
    OracleCovered rowCases1046 p outcome := by
  cases h255 : p 255 with
  | false =>
    cases h10255 : p 10255 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_south, advanceAt255_east, advanceAt255_southEast, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, cornerAt255_southEast, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_south, advanceAt255_east, advanceAt255_southEast, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, cornerAt255_southEast, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_south, advanceAt255_east, advanceAt255_southEast, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, cornerAt255_southEast, h255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1047 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .southWest = some outcome) :
    OracleCovered rowCases1047 p outcome := by
  cases h255 : p 255 with
  | false =>
    cases h10255 : p 10255 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_south, advanceAt255_west, advanceAt255_southWest, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, cornerAt255_southWest, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_south, advanceAt255_west, advanceAt255_southWest, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, cornerAt255_southWest, h255, h10255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt255_south, advanceAt255_west, advanceAt255_southWest, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, cornerAt255_southWest, h255, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1048 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 256 .north = some outcome) :
    OracleCovered rowCases1048 p outcome := by
  cases h256 : p 256 with
  | false =>
    cases h10256 : p 10256 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 256 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt14_north, advanceAt36_north, advanceAt58_north, advanceAt80_north, advanceAt102_north, advanceAt124_north, advanceAt146_north, advanceAt168_north, advanceAt190_north, advanceAt212_north, advanceAt234_north, advanceAt234_south, advanceAt256_north, floorAt14, doorAt14, trapAt14, boxAt14, holeAt14, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, cornerAt256_north, h256, h10256, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 256 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt14_north, advanceAt36_north, advanceAt58_north, advanceAt80_north, advanceAt102_north, advanceAt124_north, advanceAt146_north, advanceAt168_north, advanceAt190_north, advanceAt212_north, advanceAt234_north, advanceAt234_south, advanceAt256_north, floorAt14, doorAt14, trapAt14, boxAt14, holeAt14, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, cornerAt256_north, h256, h10256, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 256 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt14_north, advanceAt36_north, advanceAt58_north, advanceAt80_north, advanceAt102_north, advanceAt124_north, advanceAt146_north, advanceAt168_north, advanceAt190_north, advanceAt212_north, advanceAt234_north, advanceAt234_south, advanceAt256_north, floorAt14, doorAt14, trapAt14, boxAt14, holeAt14, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, cornerAt256_north, h256, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1049 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 256 .south = some outcome) :
    OracleCovered rowCases1049 p outcome := by
  cases h256 : p 256 with
  | false =>
    cases h10256 : p 10256 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 256 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt256_south, advanceAt278_north, advanceAt278_south, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, cornerAt256_south, h256, h10256, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 256 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt256_south, advanceAt278_north, advanceAt278_south, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, cornerAt256_south, h256, h10256, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 256 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt256_south, advanceAt278_north, advanceAt278_south, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, cornerAt256_south, h256, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko22Hazard87
