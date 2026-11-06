import NetHack.Soko22Hazard87.OracleCover010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover385 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .south = some outcome) :
    OracleCovered rowCases385 p outcome := by
  cases h118 : p 118 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_south, advanceAt140_north, advanceAt140_south, advanceAt162_south, advanceAt184_south, advanceAt206_south, advanceAt228_south, advanceAt250_south, advanceAt272_south, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt118_south, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_south, advanceAt140_north, advanceAt140_south, advanceAt162_south, advanceAt184_south, advanceAt206_south, advanceAt228_south, advanceAt250_south, advanceAt272_south, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt118_south, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover386 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .east = some outcome) :
    OracleCovered rowCases386 p outcome := by
  cases h118 : p 118 with
  | false =>
    cases h119 : p 119 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .east = some (.walk 119) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_east, advanceAt119_east, advanceAt119_west, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt118_east, h118, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 119) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 119), d100937), oracleMember361, same, ?_⟩
      simp only [d82372, d100937, d0, d1, h118, h119, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h120 : p 120 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .east = some (.push 119 (.stay 120)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_east, advanceAt119_east, advanceAt119_west, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt118_east, h118, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 119 (.stay 120)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 119 (.stay 120)), d100940), oracleMember362, same, ?_⟩
        simp only [d82371, d100939, d100940, d0, d1, h118, h119, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_east, advanceAt119_east, advanceAt119_west, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt118_east, h118, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_east, advanceAt119_east, advanceAt119_west, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt118_east, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover387 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .west = some outcome) :
    OracleCovered rowCases387 p outcome := by
  cases h118 : p 118 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_west, advanceAt116_west, advanceAt117_east, advanceAt117_west, advanceAt118_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, cornerAt118_west, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_west, advanceAt116_west, advanceAt117_east, advanceAt117_west, advanceAt118_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, cornerAt118_west, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover388 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northEast = some outcome) :
    OracleCovered rowCases388 p outcome := by
  cases h118 : p 118 with
  | false =>
    cases h96 : p 96 with
    | false =>
      cases h97 : p 97 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northEast = some (.walk 97) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_north, advanceAt118_east, advanceAt118_northEast, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt118_northEast, h96, h97, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 97) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 97), d82414), oracleMember363, same, ?_⟩
        simp only [d82372, d82411, d82413, d82414, d0, d1, h96, h97, h118, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_north, advanceAt118_east, advanceAt118_northEast, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt118_northEast, h96, h97, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h119 : p 119 with
      | false =>
        cases h97 : p 97 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northEast = some (.walk 97) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_north, advanceAt118_east, advanceAt118_northEast, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt118_northEast, h96, h97, h118, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 97) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 97), d82414), oracleMember363, same, ?_⟩
          simp only [d82372, d82411, d82413, d82414, d0, d1, h96, h97, h118, h119, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_north, advanceAt118_east, advanceAt118_northEast, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt118_northEast, h96, h97, h118, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_north, advanceAt118_east, advanceAt118_northEast, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt118_northEast, h96, h118, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_north, advanceAt118_east, advanceAt118_northEast, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt118_northEast, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover389 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northWest = some outcome) :
    OracleCovered rowCases389 p outcome := by
  cases h118 : p 118 with
  | false =>
    cases h96 : p 96 with
    | false =>
      cases h95 : p 95 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northWest = some (.walk 95) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_north, advanceAt118_west, advanceAt118_northWest, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, cornerAt118_northWest, h95, h96, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 95) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 95), d82360), oracleMember364, same, ?_⟩
        simp only [d66277, d74044, d82360, d0, d1, h95, h96, h118, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_north, advanceAt118_west, advanceAt118_northWest, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, cornerAt118_northWest, h95, h96, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_north, advanceAt118_west, advanceAt118_northWest, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, cornerAt118_northWest, h96, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_north, advanceAt118_west, advanceAt118_northWest, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, cornerAt118_northWest, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover390 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .southEast = some outcome) :
    OracleCovered rowCases390 p outcome := by
  cases h118 : p 118 with
  | false =>
    cases h119 : p 119 with
    | false =>
      cases h141 : p 141 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .southEast = some (.walk 141) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_south, advanceAt118_east, advanceAt118_southEast, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt118_southEast, h118, h119, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 141) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 141), d100942), oracleMember365, same, ?_⟩
        simp only [d82378, d100941, d100942, d0, d1, h118, h119, h141, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_south, advanceAt118_east, advanceAt118_southEast, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt118_southEast, h118, h119, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_south, advanceAt118_east, advanceAt118_southEast, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt118_southEast, h118, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_south, advanceAt118_east, advanceAt118_southEast, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt118_southEast, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover391 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .southWest = some outcome) :
    OracleCovered rowCases391 p outcome := by
  cases h118 : p 118 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_south, advanceAt118_west, advanceAt118_southWest, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt118_southWest, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt118_south, advanceAt118_west, advanceAt118_southWest, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt118_southWest, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover392 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .north = some outcome) :
    OracleCovered rowCases392 p outcome := by
  cases h119 : p 119 with
  | false =>
    cases h97 : p 97 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .north = some (.walk 97) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt9_north, advanceAt31_north, advanceAt53_north, advanceAt75_north, advanceAt97_north, advanceAt97_south, advanceAt119_north, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt119_north, h97, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 97) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 97), d82376), oracleMember366, same, ?_⟩
      simp only [d82372, d82376, d0, d1, h97, h119, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt9_north, advanceAt31_north, advanceAt53_north, advanceAt75_north, advanceAt97_north, advanceAt97_south, advanceAt119_north, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt119_north, h97, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt9_north, advanceAt31_north, advanceAt53_north, advanceAt75_north, advanceAt97_north, advanceAt97_south, advanceAt119_north, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt119_north, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover393 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .south = some outcome) :
    OracleCovered rowCases393 p outcome := by
  cases h119 : p 119 with
  | false =>
    cases h141 : p 141 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .south = some (.walk 141) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_south, advanceAt141_north, advanceAt141_south, advanceAt163_south, advanceAt185_south, advanceAt207_south, advanceAt229_south, advanceAt251_south, advanceAt273_south, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt119_south, h119, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 141) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 141), d100941), oracleMember367, same, ?_⟩
      simp only [d82378, d100941, d0, d1, h119, h141, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h163 : p 163 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .south = some (.push 141 (.stay 163)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_south, advanceAt141_north, advanceAt141_south, advanceAt163_south, advanceAt185_south, advanceAt207_south, advanceAt229_south, advanceAt251_south, advanceAt273_south, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt119_south, h119, h141, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 141 (.stay 163)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 141 (.stay 163)), d102055), oracleMember368, same, ?_⟩
        simp only [d102052, d102054, d102055, d0, d1, h119, h141, h163, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_south, advanceAt141_north, advanceAt141_south, advanceAt163_south, advanceAt185_south, advanceAt207_south, advanceAt229_south, advanceAt251_south, advanceAt273_south, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt119_south, h119, h141, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_south, advanceAt141_north, advanceAt141_south, advanceAt163_south, advanceAt185_south, advanceAt207_south, advanceAt229_south, advanceAt251_south, advanceAt273_south, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt119_south, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover394 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .east = some outcome) :
    OracleCovered rowCases394 p outcome := by
  cases h119 : p 119 with
  | false =>
    cases h120 : p 120 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .east = some (.walk 120) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_east, advanceAt120_east, advanceAt120_west, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt119_east, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 120) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 120), d82407), oracleMember369, same, ?_⟩
      simp only [d82372, d82407, d0, d1, h119, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_east, advanceAt120_east, advanceAt120_west, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt119_east, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_east, advanceAt120_east, advanceAt120_west, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt119_east, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover395 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .west = some outcome) :
    OracleCovered rowCases395 p outcome := by
  cases h119 : p 119 with
  | false =>
    cases h118 : p 118 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .west = some (.walk 118) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_west, advanceAt116_west, advanceAt117_west, advanceAt118_east, advanceAt118_west, advanceAt119_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt119_west, h118, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 118) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 118), d100937), oracleMember370, same, ?_⟩
      simp only [d82372, d100937, d0, d1, h118, h119, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_west, advanceAt116_west, advanceAt117_west, advanceAt118_east, advanceAt118_west, advanceAt119_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt119_west, h118, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_west, advanceAt116_west, advanceAt117_west, advanceAt118_east, advanceAt118_west, advanceAt119_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt119_west, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover396 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northEast = some outcome) :
    OracleCovered rowCases396 p outcome := by
  cases h119 : p 119 with
  | false =>
    cases h97 : p 97 with
    | false =>
      cases h98 : p 98 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northEast = some (.walk 98) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_north, advanceAt119_east, advanceAt119_northEast, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt119_northEast, h97, h98, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 98) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 98), d82422), oracleMember371, same, ?_⟩
        simp only [d82372, d82407, d82420, d82421, d82422, d0, d1, h97, h98, h119, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_north, advanceAt119_east, advanceAt119_northEast, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt119_northEast, h97, h98, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h120 : p 120 with
      | false =>
        cases h98 : p 98 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northEast = some (.walk 98) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_north, advanceAt119_east, advanceAt119_northEast, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt119_northEast, h97, h98, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 98) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 98), d82422), oracleMember371, same, ?_⟩
          simp only [d82372, d82407, d82420, d82421, d82422, d0, d1, h97, h98, h119, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_north, advanceAt119_east, advanceAt119_northEast, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt119_northEast, h97, h98, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_north, advanceAt119_east, advanceAt119_northEast, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt119_northEast, h97, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_north, advanceAt119_east, advanceAt119_northEast, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt119_northEast, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover397 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northWest = some outcome) :
    OracleCovered rowCases397 p outcome := by
  cases h119 : p 119 with
  | false =>
    cases h97 : p 97 with
    | false =>
      cases h96 : p 96 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northWest = some (.walk 96) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_north, advanceAt119_west, advanceAt119_northWest, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt119_northWest, h96, h97, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 96) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 96), d82375), oracleMember372, same, ?_⟩
        simp only [d82372, d82373, d82374, d82375, d0, d1, h96, h97, h119, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_north, advanceAt119_west, advanceAt119_northWest, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt119_northWest, h96, h97, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h118 : p 118 with
      | false =>
        cases h96 : p 96 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northWest = some (.walk 96) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_north, advanceAt119_west, advanceAt119_northWest, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt119_northWest, h96, h97, h118, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 96) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 96), d82375), oracleMember372, same, ?_⟩
          simp only [d82372, d82373, d82374, d82375, d0, d1, h96, h97, h118, h119, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_north, advanceAt119_west, advanceAt119_northWest, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt119_northWest, h96, h97, h118, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_north, advanceAt119_west, advanceAt119_northWest, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt119_northWest, h97, h118, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_north, advanceAt119_west, advanceAt119_northWest, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, cornerAt119_northWest, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover398 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .southEast = some outcome) :
    OracleCovered rowCases398 p outcome := by
  cases h119 : p 119 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_south, advanceAt119_east, advanceAt119_southEast, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt119_southEast, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_south, advanceAt119_east, advanceAt119_southEast, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt119_southEast, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover399 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .southWest = some outcome) :
    OracleCovered rowCases399 p outcome := by
  cases h119 : p 119 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_south, advanceAt119_west, advanceAt119_southWest, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt119_southWest, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt119_south, advanceAt119_west, advanceAt119_southWest, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt119_southWest, h119, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover400 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .north = some outcome) :
    OracleCovered rowCases400 p outcome := by
  cases h120 : p 120 with
  | false =>
    cases h98 : p 98 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .north = some (.walk 98) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt32_north, advanceAt54_north, advanceAt76_north, advanceAt98_north, advanceAt98_south, advanceAt120_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_north, h98, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 98) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 98), d82415), oracleMember373, same, ?_⟩
      simp only [d74069, d82415, d0, d1, h98, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h76 : p 76 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .north = some (.push 98 (.stay 76)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt32_north, advanceAt54_north, advanceAt76_north, advanceAt98_north, advanceAt98_south, advanceAt120_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_north, h76, h98, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 98 (.stay 76)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 98 (.stay 76)), d74072), oracleMember374, same, ?_⟩
        simp only [d74069, d74071, d74072, d0, d1, h76, h98, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt32_north, advanceAt54_north, advanceAt76_north, advanceAt98_north, advanceAt98_south, advanceAt120_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_north, h76, h98, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt32_north, advanceAt54_north, advanceAt76_north, advanceAt98_north, advanceAt98_south, advanceAt120_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_north, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover401 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .south = some outcome) :
    OracleCovered rowCases401 p outcome := by
  cases h120 : p 120 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_south, advanceAt142_north, advanceAt142_south, advanceAt164_south, advanceAt186_south, advanceAt208_south, advanceAt230_south, advanceAt252_south, advanceAt274_south, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt120_south, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_south, advanceAt142_north, advanceAt142_south, advanceAt164_south, advanceAt186_south, advanceAt208_south, advanceAt230_south, advanceAt252_south, advanceAt274_south, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt120_south, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover402 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .east = some outcome) :
    OracleCovered rowCases402 p outcome := by
  cases h120 : p 120 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_east, advanceAt121_east, advanceAt121_west, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt120_east, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_east, advanceAt121_east, advanceAt121_west, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt120_east, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover403 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .west = some outcome) :
    OracleCovered rowCases403 p outcome := by
  cases h120 : p 120 with
  | false =>
    cases h119 : p 119 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .west = some (.walk 119) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_west, advanceAt116_west, advanceAt117_west, advanceAt118_west, advanceAt119_east, advanceAt119_west, advanceAt120_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_west, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 119) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 119), d82407), oracleMember375, same, ?_⟩
      simp only [d82372, d82407, d0, d1, h119, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h118 : p 118 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .west = some (.push 119 (.stay 118)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_west, advanceAt116_west, advanceAt117_west, advanceAt118_west, advanceAt119_east, advanceAt119_west, advanceAt120_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_west, h118, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 119 (.stay 118)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 119 (.stay 118)), d100940), oracleMember376, same, ?_⟩
        simp only [d82371, d100939, d100940, d0, d1, h118, h119, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_west, advanceAt116_west, advanceAt117_west, advanceAt118_west, advanceAt119_east, advanceAt119_west, advanceAt120_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_west, h118, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_west, advanceAt116_west, advanceAt117_west, advanceAt118_west, advanceAt119_east, advanceAt119_west, advanceAt120_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_west, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover404 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .northEast = some outcome) :
    OracleCovered rowCases404 p outcome := by
  cases h120 : p 120 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_north, advanceAt120_east, advanceAt120_northEast, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, cornerAt120_northEast, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_north, advanceAt120_east, advanceAt120_northEast, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, cornerAt120_northEast, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover405 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .northWest = some outcome) :
    OracleCovered rowCases405 p outcome := by
  cases h120 : p 120 with
  | false =>
    cases h98 : p 98 with
    | false =>
      cases h97 : p 97 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .northWest = some (.walk 97) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_north, advanceAt120_west, advanceAt120_northWest, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_northWest, h97, h98, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 97) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 97), d82409), oracleMember377, same, ?_⟩
        simp only [d74069, d82372, d82407, d82408, d82409, d0, d1, h97, h98, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_north, advanceAt120_west, advanceAt120_northWest, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_northWest, h97, h98, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h119 : p 119 with
      | false =>
        cases h97 : p 97 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .northWest = some (.walk 97) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_north, advanceAt120_west, advanceAt120_northWest, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_northWest, h97, h98, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 97) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 97), d82409), oracleMember377, same, ?_⟩
          simp only [d74069, d82372, d82407, d82408, d82409, d0, d1, h97, h98, h119, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_north, advanceAt120_west, advanceAt120_northWest, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_northWest, h97, h98, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_north, advanceAt120_west, advanceAt120_northWest, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_northWest, h98, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_north, advanceAt120_west, advanceAt120_northWest, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, cornerAt120_northWest, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover406 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .southEast = some outcome) :
    OracleCovered rowCases406 p outcome := by
  cases h120 : p 120 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_south, advanceAt120_east, advanceAt120_southEast, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt120_southEast, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_south, advanceAt120_east, advanceAt120_southEast, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt120_southEast, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover407 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .southWest = some outcome) :
    OracleCovered rowCases407 p outcome := by
  cases h120 : p 120 with
  | false =>
    cases h119 : p 119 with
    | false =>
      cases h141 : p 141 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .southWest = some (.walk 141) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_south, advanceAt120_west, advanceAt120_southWest, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt120_southWest, h119, h120, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 141) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 141), d102105), oracleMember378, same, ?_⟩
        simp only [d82378, d100941, d102105, d0, d1, h119, h120, h141, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_south, advanceAt120_west, advanceAt120_southWest, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt120_southWest, h119, h120, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_south, advanceAt120_west, advanceAt120_southWest, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt120_southWest, h119, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt120_south, advanceAt120_west, advanceAt120_southWest, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt120_southWest, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover408 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .north = some outcome) :
    OracleCovered rowCases408 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .north = some (.walk 100) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt34_north, advanceAt56_north, advanceAt78_north, advanceAt100_north, advanceAt100_south, advanceAt122_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, cornerAt122_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 100) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 100), d1), oracleMember379, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover409 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .south = some outcome) :
    OracleCovered rowCases409 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .south = some (.walk 144) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt122_south, advanceAt144_north, advanceAt144_south, advanceAt166_south, advanceAt188_south, advanceAt210_south, advanceAt232_south, advanceAt254_south, advanceAt276_south, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, cornerAt122_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 144) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 144), d1), oracleMember381, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover410 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .east = some outcome) :
    OracleCovered rowCases410 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .east = some (.walk 123) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt122_east, advanceAt123_east, advanceAt123_west, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt122_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 123) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 123), d1), oracleMember383, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover411 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .west = some outcome) :
    OracleCovered rowCases411 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .west = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_west, advanceAt116_west, advanceAt117_west, advanceAt118_west, advanceAt119_west, advanceAt120_west, advanceAt121_east, advanceAt121_west, advanceAt122_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, cornerAt122_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover412 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .northEast = some outcome) :
    OracleCovered rowCases412 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .northEast = some (.walk 101) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt122_north, advanceAt122_east, advanceAt122_northEast, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, cornerAt122_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 101) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 101), d1), oracleMember385, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover413 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .northWest = some outcome) :
    OracleCovered rowCases413 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .northWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt122_north, advanceAt122_west, advanceAt122_northWest, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, cornerAt122_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover414 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .southEast = some outcome) :
    OracleCovered rowCases414 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .southEast = some (.walk 145) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt122_south, advanceAt122_east, advanceAt122_southEast, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, cornerAt122_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 145) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 145), d1), oracleMember386, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover415 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .southWest = some outcome) :
    OracleCovered rowCases415 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 .southWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt122_south, advanceAt122_west, advanceAt122_southWest, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, cornerAt122_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover416 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 123 .north = some outcome) :
    OracleCovered rowCases416 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 123 .north = some (.walk 101) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt13_north, advanceAt35_north, advanceAt57_north, advanceAt79_north, advanceAt101_north, advanceAt101_south, advanceAt123_north, floorAt13, doorAt13, trapAt13, boxAt13, holeAt13, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, cornerAt123_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 101) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 101), d1), oracleMember387, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover417 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 123 .south = some outcome) :
    OracleCovered rowCases417 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 123 .south = some (.walk 145) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt123_south, advanceAt145_north, advanceAt145_south, advanceAt167_south, advanceAt189_south, advanceAt211_south, advanceAt233_south, advanceAt255_south, advanceAt277_south, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, cornerAt123_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 145) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 145), d1), oracleMember389, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover418 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 123 .east = some outcome) :
    OracleCovered rowCases418 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 123 .east = some (.walk 124) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt123_east, advanceAt124_east, advanceAt124_west, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt123_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 124) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 124), d1), oracleMember391, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover419 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 123 .west = some outcome) :
    OracleCovered rowCases419 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 123 .west = some (.walk 122) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_west, advanceAt116_west, advanceAt117_west, advanceAt118_west, advanceAt119_west, advanceAt120_west, advanceAt121_west, advanceAt122_east, advanceAt122_west, advanceAt123_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, cornerAt123_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 122) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 122), d1), oracleMember393, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
end NetHack.Soko22Hazard87
