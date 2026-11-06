import NetHack.Soko22Hazard87.OracleCover007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover280 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .north = some outcome) :
    OracleCovered rowCases280 p outcome := by
  cases h98 : p 98 with
  | false =>
    cases h76 : p 76 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .north = some (.walk 76) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt32_north, advanceAt54_north, advanceAt76_north, advanceAt76_south, advanceAt98_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt98_north, h76, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 76) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 76), d74067), oracleMember249, same, ?_⟩
      simp only [d74066, d74067, d0, d1, h76, h98, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt32_north, advanceAt54_north, advanceAt76_north, advanceAt76_south, advanceAt98_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt98_north, h76, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt32_north, advanceAt54_north, advanceAt76_north, advanceAt76_south, advanceAt98_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt98_north, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover281 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .south = some outcome) :
    OracleCovered rowCases281 p outcome := by
  cases h98 : p 98 with
  | false =>
    cases h120 : p 120 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .south = some (.walk 120) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_south, advanceAt120_north, advanceAt120_south, advanceAt142_south, advanceAt164_south, advanceAt186_south, advanceAt208_south, advanceAt230_south, advanceAt252_south, advanceAt274_south, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt98_south, h98, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 120) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 120), d82415), oracleMember250, same, ?_⟩
      simp only [d74069, d82415, d0, d1, h98, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_south, advanceAt120_north, advanceAt120_south, advanceAt142_south, advanceAt164_south, advanceAt186_south, advanceAt208_south, advanceAt230_south, advanceAt252_south, advanceAt274_south, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt98_south, h98, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_south, advanceAt120_north, advanceAt120_south, advanceAt142_south, advanceAt164_south, advanceAt186_south, advanceAt208_south, advanceAt230_south, advanceAt252_south, advanceAt274_south, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt98_south, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover282 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .east = some outcome) :
    OracleCovered rowCases282 p outcome := by
  cases h98 : p 98 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_east, advanceAt99_east, advanceAt99_west, advanceAt100_east, advanceAt101_east, advanceAt102_east, advanceAt103_east, advanceAt104_east, advanceAt105_east, advanceAt106_east, advanceAt107_east, advanceAt108_east, advanceAt109_east, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, cornerAt98_east, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_east, advanceAt99_east, advanceAt99_west, advanceAt100_east, advanceAt101_east, advanceAt102_east, advanceAt103_east, advanceAt104_east, advanceAt105_east, advanceAt106_east, advanceAt107_east, advanceAt108_east, advanceAt109_east, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, cornerAt98_east, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover283 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .west = some outcome) :
    OracleCovered rowCases283 p outcome := by
  cases h98 : p 98 with
  | false =>
    cases h97 : p 97 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .west = some (.walk 97) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt88_west, advanceAt89_west, advanceAt90_west, advanceAt91_west, advanceAt92_west, advanceAt93_west, advanceAt94_west, advanceAt95_west, advanceAt96_west, advanceAt97_east, advanceAt97_west, advanceAt98_west, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt98_west, h97, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 97) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 97), d74073), oracleMember251, same, ?_⟩
      simp only [d74066, d74073, d0, d1, h97, h98, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h96 : p 96 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .west = some (.push 97 (.stay 96)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt88_west, advanceAt89_west, advanceAt90_west, advanceAt91_west, advanceAt92_west, advanceAt93_west, advanceAt94_west, advanceAt95_west, advanceAt96_west, advanceAt97_east, advanceAt97_west, advanceAt98_west, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt98_west, h96, h97, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 97 (.stay 96)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 97 (.stay 96)), d82367), oracleMember252, same, ?_⟩
        simp only [d66277, d82366, d82367, d0, d1, h96, h97, h98, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt88_west, advanceAt89_west, advanceAt90_west, advanceAt91_west, advanceAt92_west, advanceAt93_west, advanceAt94_west, advanceAt95_west, advanceAt96_west, advanceAt97_east, advanceAt97_west, advanceAt98_west, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt98_west, h96, h97, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt88_west, advanceAt89_west, advanceAt90_west, advanceAt91_west, advanceAt92_west, advanceAt93_west, advanceAt94_west, advanceAt95_west, advanceAt96_west, advanceAt97_east, advanceAt97_west, advanceAt98_west, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt98_west, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover284 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .northEast = some outcome) :
    OracleCovered rowCases284 p outcome := by
  cases h98 : p 98 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_north, advanceAt98_east, advanceAt98_northEast, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, cornerAt98_northEast, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_north, advanceAt98_east, advanceAt98_northEast, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, cornerAt98_northEast, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover285 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .northWest = some outcome) :
    OracleCovered rowCases285 p outcome := by
  cases h98 : p 98 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_north, advanceAt98_west, advanceAt98_northWest, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt98_northWest, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_north, advanceAt98_west, advanceAt98_northWest, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt98_northWest, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover286 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .southEast = some outcome) :
    OracleCovered rowCases286 p outcome := by
  cases h98 : p 98 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_south, advanceAt98_east, advanceAt98_southEast, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, cornerAt98_southEast, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_south, advanceAt98_east, advanceAt98_southEast, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, cornerAt98_southEast, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover287 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .southWest = some outcome) :
    OracleCovered rowCases287 p outcome := by
  cases h98 : p 98 with
  | false =>
    cases h120 : p 120 with
    | false =>
      cases h119 : p 119 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .southWest = some (.walk 119) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_south, advanceAt98_west, advanceAt98_southWest, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt98_southWest, h98, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 119) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 119), d82422), oracleMember253, same, ?_⟩
        simp only [d82372, d82407, d82420, d82421, d82422, d0, d1, h98, h119, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_south, advanceAt98_west, advanceAt98_southWest, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt98_southWest, h98, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h97 : p 97 with
      | false =>
        cases h119 : p 119 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .southWest = some (.walk 119) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_south, advanceAt98_west, advanceAt98_southWest, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt98_southWest, h97, h98, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 119) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 119), d82422), oracleMember253, same, ?_⟩
          simp only [d82372, d82407, d82420, d82421, d82422, d0, d1, h97, h98, h119, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_south, advanceAt98_west, advanceAt98_southWest, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt98_southWest, h97, h98, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_south, advanceAt98_west, advanceAt98_southWest, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt98_southWest, h97, h98, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt98_south, advanceAt98_west, advanceAt98_southWest, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt98_southWest, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover288 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .north = some outcome) :
    OracleCovered rowCases288 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .north = some (.walk 78) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt34_north, advanceAt56_north, advanceAt78_north, advanceAt78_south, advanceAt100_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, cornerAt100_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 78) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 78), d1), oracleMember254, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover289 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .south = some outcome) :
    OracleCovered rowCases289 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .south = some (.walk 122) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt100_south, advanceAt122_north, advanceAt122_south, advanceAt144_south, advanceAt166_south, advanceAt188_south, advanceAt210_south, advanceAt232_south, advanceAt254_south, advanceAt276_south, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, cornerAt100_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 122) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 122), d1), oracleMember255, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover290 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .east = some outcome) :
    OracleCovered rowCases290 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .east = some (.walk 101) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt100_east, advanceAt101_east, advanceAt101_west, advanceAt102_east, advanceAt103_east, advanceAt104_east, advanceAt105_east, advanceAt106_east, advanceAt107_east, advanceAt108_east, advanceAt109_east, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, cornerAt100_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 101) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 101), d1), oracleMember257, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover291 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .west = some outcome) :
    OracleCovered rowCases291 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .west = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt88_west, advanceAt89_west, advanceAt90_west, advanceAt91_west, advanceAt92_west, advanceAt93_west, advanceAt94_west, advanceAt95_west, advanceAt96_west, advanceAt97_west, advanceAt98_west, advanceAt99_east, advanceAt99_west, advanceAt100_west, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, cornerAt100_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover292 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .northEast = some outcome) :
    OracleCovered rowCases292 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .northEast = some (.walk 79) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt100_north, advanceAt100_east, advanceAt100_northEast, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, cornerAt100_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 79) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 79), d1), oracleMember259, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover293 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .northWest = some outcome) :
    OracleCovered rowCases293 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .northWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt100_north, advanceAt100_west, advanceAt100_northWest, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, cornerAt100_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover294 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .southEast = some outcome) :
    OracleCovered rowCases294 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .southEast = some (.walk 123) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt100_south, advanceAt100_east, advanceAt100_southEast, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, cornerAt100_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 123) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 123), d1), oracleMember260, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover295 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .southWest = some outcome) :
    OracleCovered rowCases295 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .southWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt100_south, advanceAt100_west, advanceAt100_southWest, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, cornerAt100_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover296 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .north = some outcome) :
    OracleCovered rowCases296 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .north = some (.walk 79) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt13_north, advanceAt35_north, advanceAt57_north, advanceAt79_north, advanceAt79_south, advanceAt101_north, floorAt13, doorAt13, trapAt13, boxAt13, holeAt13, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, cornerAt101_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 79) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 79), d1), oracleMember261, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover297 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .south = some outcome) :
    OracleCovered rowCases297 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .south = some (.walk 123) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt101_south, advanceAt123_north, advanceAt123_south, advanceAt145_south, advanceAt167_south, advanceAt189_south, advanceAt211_south, advanceAt233_south, advanceAt255_south, advanceAt277_south, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, cornerAt101_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 123) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 123), d1), oracleMember262, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover298 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .east = some outcome) :
    OracleCovered rowCases298 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .east = some (.walk 102) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt101_east, advanceAt102_east, advanceAt102_west, advanceAt103_east, advanceAt104_east, advanceAt105_east, advanceAt106_east, advanceAt107_east, advanceAt108_east, advanceAt109_east, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, cornerAt101_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 102) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 102), d1), oracleMember264, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover299 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .west = some outcome) :
    OracleCovered rowCases299 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .west = some (.walk 100) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt88_west, advanceAt89_west, advanceAt90_west, advanceAt91_west, advanceAt92_west, advanceAt93_west, advanceAt94_west, advanceAt95_west, advanceAt96_west, advanceAt97_west, advanceAt98_west, advanceAt99_west, advanceAt100_east, advanceAt100_west, advanceAt101_west, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, cornerAt101_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 100) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 100), d1), oracleMember266, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover300 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .northEast = some outcome) :
    OracleCovered rowCases300 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .northEast = some (.walk 80) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt101_north, advanceAt101_east, advanceAt101_northEast, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, cornerAt101_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 80) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 80), d1), oracleMember267, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover301 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .northWest = some outcome) :
    OracleCovered rowCases301 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .northWest = some (.walk 78) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt101_north, advanceAt101_west, advanceAt101_northWest, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, cornerAt101_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 78) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 78), d1), oracleMember268, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover302 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .southEast = some outcome) :
    OracleCovered rowCases302 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .southEast = some (.walk 124) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt101_south, advanceAt101_east, advanceAt101_southEast, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, cornerAt101_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 124) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 124), d1), oracleMember269, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover303 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .southWest = some outcome) :
    OracleCovered rowCases303 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .southWest = some (.walk 122) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt101_south, advanceAt101_west, advanceAt101_southWest, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, cornerAt101_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 122) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 122), d1), oracleMember270, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover304 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .north = some outcome) :
    OracleCovered rowCases304 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .north = some (.walk 80) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt14_north, advanceAt36_north, advanceAt58_north, advanceAt80_north, advanceAt80_south, advanceAt102_north, floorAt14, doorAt14, trapAt14, boxAt14, holeAt14, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, cornerAt102_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 80) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 80), d1), oracleMember271, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover305 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .south = some outcome) :
    OracleCovered rowCases305 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .south = some (.walk 124) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt102_south, advanceAt124_north, advanceAt124_south, advanceAt146_south, advanceAt168_south, advanceAt190_south, advanceAt212_south, advanceAt234_south, advanceAt256_south, advanceAt278_south, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, cornerAt102_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 124) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 124), d1), oracleMember272, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover306 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .east = some outcome) :
    OracleCovered rowCases306 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .east = some (.walk 103) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt102_east, advanceAt103_east, advanceAt103_west, advanceAt104_east, advanceAt105_east, advanceAt106_east, advanceAt107_east, advanceAt108_east, advanceAt109_east, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, cornerAt102_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 103) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 103), d1), oracleMember274, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover307 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .west = some outcome) :
    OracleCovered rowCases307 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .west = some (.walk 101) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt88_west, advanceAt89_west, advanceAt90_west, advanceAt91_west, advanceAt92_west, advanceAt93_west, advanceAt94_west, advanceAt95_west, advanceAt96_west, advanceAt97_west, advanceAt98_west, advanceAt99_west, advanceAt100_west, advanceAt101_east, advanceAt101_west, advanceAt102_west, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, cornerAt102_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 101) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 101), d1), oracleMember276, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover308 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .northEast = some outcome) :
    OracleCovered rowCases308 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .northEast = some (.walk 81) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt102_north, advanceAt102_east, advanceAt102_northEast, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, cornerAt102_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 81) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 81), d1), oracleMember278, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover309 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .northWest = some outcome) :
    OracleCovered rowCases309 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .northWest = some (.walk 79) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt102_north, advanceAt102_west, advanceAt102_northWest, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, cornerAt102_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 79) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 79), d1), oracleMember279, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover310 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .southEast = some outcome) :
    OracleCovered rowCases310 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .southEast = some (.walk 125) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt102_south, advanceAt102_east, advanceAt102_southEast, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, cornerAt102_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 125) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 125), d1), oracleMember280, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover311 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .southWest = some outcome) :
    OracleCovered rowCases311 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .southWest = some (.walk 123) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt102_south, advanceAt102_west, advanceAt102_southWest, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, cornerAt102_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 123) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 123), d1), oracleMember281, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover312 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .north = some outcome) :
    OracleCovered rowCases312 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .north = some (.walk 81) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt15_north, advanceAt37_north, advanceAt59_north, advanceAt81_north, advanceAt81_south, advanceAt103_north, floorAt15, doorAt15, trapAt15, boxAt15, holeAt15, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, cornerAt103_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 81) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 81), d1), oracleMember282, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover313 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .south = some outcome) :
    OracleCovered rowCases313 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .south = some (.walk 125) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt103_south, advanceAt125_north, advanceAt125_south, advanceAt147_south, advanceAt169_south, advanceAt191_south, advanceAt213_south, advanceAt235_south, advanceAt257_south, advanceAt279_south, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, cornerAt103_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 125) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 125), d1), oracleMember283, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover314 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .east = some outcome) :
    OracleCovered rowCases314 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .east = some (.walk 104) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt103_east, advanceAt104_east, advanceAt104_west, advanceAt105_east, advanceAt106_east, advanceAt107_east, advanceAt108_east, advanceAt109_east, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, cornerAt103_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 104) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 104), d1), oracleMember285, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
end NetHack.Soko22Hazard87
