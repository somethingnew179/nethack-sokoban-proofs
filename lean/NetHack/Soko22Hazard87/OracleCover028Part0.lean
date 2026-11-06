import NetHack.Soko22Hazard87.OracleCover027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover980 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northEast = some outcome) :
    OracleCovered rowCases980 p outcome := by
  cases h247 : p 247 with
  | false =>
    cases h225 : p 225 with
    | false =>
      cases h226 : p 226 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northEast = some (.walk 226) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_north, advanceAt247_east, advanceAt247_northEast, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt247_northEast, h225, h226, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 226) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 226), d331335), oracleMember979, same, ?_⟩
        simp only [d13, d14, d253504, d271213, d331334, d331335, d0, d1, h225, h226, h247, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_north, advanceAt247_east, advanceAt247_northEast, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt247_northEast, h225, h226, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h248 : p 248 with
      | false =>
        cases h226 : p 226 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northEast = some (.walk 226) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_north, advanceAt247_east, advanceAt247_northEast, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt247_northEast, h225, h226, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 226) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 226), d331335), oracleMember979, same, ?_⟩
          simp only [d13, d14, d253504, d271213, d331334, d331335, d0, d1, h225, h226, h247, h248, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_north, advanceAt247_east, advanceAt247_northEast, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt247_northEast, h225, h226, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_north, advanceAt247_east, advanceAt247_northEast, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt247_northEast, h225, h247, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_north, advanceAt247_east, advanceAt247_northEast, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt247_northEast, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover981 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northWest = some outcome) :
    OracleCovered rowCases981 p outcome := by
  cases h247 : p 247 with
  | false =>
    cases h225 : p 225 with
    | false =>
      cases h224 : p 224 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northWest = some (.walk 224) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_north, advanceAt247_west, advanceAt247_northWest, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt247_northWest, h224, h225, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 224) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 224), d306035), oracleMember980, same, ?_⟩
        simp only [d271213, d271214, d306034, d306035, d0, d1, h224, h225, h247, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_north, advanceAt247_west, advanceAt247_northWest, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt247_northWest, h224, h225, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h246 : p 246 with
      | false =>
        cases h224 : p 224 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northWest = some (.walk 224) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_north, advanceAt247_west, advanceAt247_northWest, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt247_northWest, h224, h225, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 224) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 224), d306035), oracleMember980, same, ?_⟩
          simp only [d271213, d271214, d306034, d306035, d0, d1, h224, h225, h246, h247, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_north, advanceAt247_west, advanceAt247_northWest, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt247_northWest, h224, h225, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_north, advanceAt247_west, advanceAt247_northWest, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt247_northWest, h225, h246, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_north, advanceAt247_west, advanceAt247_northWest, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt247_northWest, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover982 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .southEast = some outcome) :
    OracleCovered rowCases982 p outcome := by
  cases h247 : p 247 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_south, advanceAt247_east, advanceAt247_southEast, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt247_southEast, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_south, advanceAt247_east, advanceAt247_southEast, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt247_southEast, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover983 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .southWest = some outcome) :
    OracleCovered rowCases983 p outcome := by
  cases h247 : p 247 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_south, advanceAt247_west, advanceAt247_southWest, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt247_southWest, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt247_south, advanceAt247_west, advanceAt247_southWest, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt247_southWest, h247, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover984 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .north = some outcome) :
    OracleCovered rowCases984 p outcome := by
  cases h248 : p 248 with
  | false =>
    cases h226 : p 226 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .north = some (.walk 226) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt28_north, advanceAt50_north, advanceAt72_north, advanceAt94_north, advanceAt116_north, advanceAt138_north, advanceAt160_north, advanceAt182_north, advanceAt204_north, advanceAt226_north, advanceAt226_south, advanceAt248_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_north, h226, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 226) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 226), d325306), oracleMember981, same, ?_⟩
      simp only [d13, d325306, d0, d1, h226, h248, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h204 : p 204 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .north = some (.push 226 (.stay 204)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt28_north, advanceAt50_north, advanceAt72_north, advanceAt94_north, advanceAt116_north, advanceAt138_north, advanceAt160_north, advanceAt182_north, advanceAt204_north, advanceAt226_north, advanceAt226_south, advanceAt248_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_north, h204, h226, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 226 (.stay 204)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 226 (.stay 204)), d271212), oracleMember982, same, ?_⟩
        simp only [d13, d271211, d271212, d0, d1, h204, h226, h248, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt28_north, advanceAt50_north, advanceAt72_north, advanceAt94_north, advanceAt116_north, advanceAt138_north, advanceAt160_north, advanceAt182_north, advanceAt204_north, advanceAt226_north, advanceAt226_south, advanceAt248_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_north, h204, h226, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt28_north, advanceAt50_north, advanceAt72_north, advanceAt94_north, advanceAt116_north, advanceAt138_north, advanceAt160_north, advanceAt182_north, advanceAt204_north, advanceAt226_north, advanceAt226_south, advanceAt248_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, cornerAt248_north, h248, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko22Hazard87
