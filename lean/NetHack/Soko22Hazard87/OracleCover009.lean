import NetHack.Soko22Hazard87.OracleCover008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover315 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .west = some outcome) :
    OracleCovered rowCases315 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .west = some (.walk 102) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt88_west, advanceAt89_west, advanceAt90_west, advanceAt91_west, advanceAt92_west, advanceAt93_west, advanceAt94_west, advanceAt95_west, advanceAt96_west, advanceAt97_west, advanceAt98_west, advanceAt99_west, advanceAt100_west, advanceAt101_west, advanceAt102_east, advanceAt102_west, advanceAt103_west, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, cornerAt103_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 102) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 102), d1), oracleMember287, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover316 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .northEast = some outcome) :
    OracleCovered rowCases316 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .northEast = some (.walk 82) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt103_north, advanceAt103_east, advanceAt103_northEast, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, cornerAt103_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 82) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 82), d1), oracleMember289, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover317 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .northWest = some outcome) :
    OracleCovered rowCases317 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .northWest = some (.walk 80) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt103_north, advanceAt103_west, advanceAt103_northWest, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, cornerAt103_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 80) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 80), d1), oracleMember290, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover318 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .southEast = some outcome) :
    OracleCovered rowCases318 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .southEast = some (.walk 126) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt103_south, advanceAt103_east, advanceAt103_southEast, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, cornerAt103_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 126) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 126), d1), oracleMember291, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover319 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .southWest = some outcome) :
    OracleCovered rowCases319 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .southWest = some (.walk 124) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt103_south, advanceAt103_west, advanceAt103_southWest, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, cornerAt103_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 124) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 124), d1), oracleMember292, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover320 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .north = some outcome) :
    OracleCovered rowCases320 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .north = some (.walk 82) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt16_north, advanceAt38_north, advanceAt60_north, advanceAt82_north, advanceAt82_south, advanceAt104_north, floorAt16, doorAt16, trapAt16, boxAt16, holeAt16, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, cornerAt104_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 82) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 82), d1), oracleMember293, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover321 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .south = some outcome) :
    OracleCovered rowCases321 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .south = some (.walk 126) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_south, advanceAt126_north, advanceAt126_south, advanceAt148_south, advanceAt170_south, advanceAt192_south, advanceAt214_south, advanceAt236_south, advanceAt258_south, advanceAt280_south, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, cornerAt104_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 126) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 126), d1), oracleMember294, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover322 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .east = some outcome) :
    OracleCovered rowCases322 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .east = some (.walk 105) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_east, advanceAt105_east, advanceAt105_west, advanceAt106_east, advanceAt107_east, advanceAt108_east, advanceAt109_east, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, cornerAt104_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 105) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 105), d1), oracleMember296, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover323 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .west = some outcome) :
    OracleCovered rowCases323 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .west = some (.walk 103) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt88_west, advanceAt89_west, advanceAt90_west, advanceAt91_west, advanceAt92_west, advanceAt93_west, advanceAt94_west, advanceAt95_west, advanceAt96_west, advanceAt97_west, advanceAt98_west, advanceAt99_west, advanceAt100_west, advanceAt101_west, advanceAt102_west, advanceAt103_east, advanceAt103_west, advanceAt104_west, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, cornerAt104_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 103) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 103), d1), oracleMember298, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover324 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .northEast = some outcome) :
    OracleCovered rowCases324 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .northEast = some (.walk 83) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_north, advanceAt104_east, advanceAt104_northEast, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, cornerAt104_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 83) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 83), d1), oracleMember300, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover325 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .northWest = some outcome) :
    OracleCovered rowCases325 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .northWest = some (.walk 81) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_north, advanceAt104_west, advanceAt104_northWest, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, cornerAt104_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 81) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 81), d1), oracleMember301, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover326 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .southEast = some outcome) :
    OracleCovered rowCases326 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .southEast = some (.walk 127) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_south, advanceAt104_east, advanceAt104_southEast, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, cornerAt104_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 127) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 127), d1), oracleMember302, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover327 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .southWest = some outcome) :
    OracleCovered rowCases327 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .southWest = some (.walk 125) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_south, advanceAt104_west, advanceAt104_southWest, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, cornerAt104_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 125) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 125), d1), oracleMember303, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover328 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .north = some outcome) :
    OracleCovered rowCases328 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .north = some (.walk 83) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt17_north, advanceAt39_north, advanceAt61_north, advanceAt83_north, advanceAt83_south, advanceAt105_north, floorAt17, doorAt17, trapAt17, boxAt17, holeAt17, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, cornerAt105_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 83) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 83), d1), oracleMember304, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover329 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .south = some outcome) :
    OracleCovered rowCases329 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .south = some (.walk 127) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt127_north, advanceAt127_south, advanceAt149_south, advanceAt171_south, advanceAt193_south, advanceAt215_south, advanceAt237_south, advanceAt259_south, advanceAt281_south, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, cornerAt105_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 127) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 127), d1), oracleMember305, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover330 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .east = some outcome) :
    OracleCovered rowCases330 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .east = some (.walk 106) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_east, advanceAt106_east, advanceAt106_west, advanceAt107_east, advanceAt108_east, advanceAt109_east, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, cornerAt105_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 106) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 106), d1), oracleMember307, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover331 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .west = some outcome) :
    OracleCovered rowCases331 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .west = some (.walk 104) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt88_west, advanceAt89_west, advanceAt90_west, advanceAt91_west, advanceAt92_west, advanceAt93_west, advanceAt94_west, advanceAt95_west, advanceAt96_west, advanceAt97_west, advanceAt98_west, advanceAt99_west, advanceAt100_west, advanceAt101_west, advanceAt102_west, advanceAt103_west, advanceAt104_east, advanceAt104_west, advanceAt105_west, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, cornerAt105_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 104) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 104), d1), oracleMember308, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover332 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .northEast = some outcome) :
    OracleCovered rowCases332 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .northEast = some (.walk 84) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_north, advanceAt105_east, advanceAt105_northEast, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt105_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 84) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 84), d1), oracleMember310, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover333 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .northWest = some outcome) :
    OracleCovered rowCases333 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .northWest = some (.walk 82) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_north, advanceAt105_west, advanceAt105_northWest, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, cornerAt105_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 82) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 82), d1), oracleMember311, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover334 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .southEast = some outcome) :
    OracleCovered rowCases334 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .southEast = some (.walk 128) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt105_east, advanceAt105_southEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, cornerAt105_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 128) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 128), d1), oracleMember312, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover335 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .southWest = some outcome) :
    OracleCovered rowCases335 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .southWest = some (.walk 126) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt105_west, advanceAt105_southWest, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, cornerAt105_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 126) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 126), d1), oracleMember313, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover336 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .north = some outcome) :
    OracleCovered rowCases336 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .north = some (.walk 84) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt18_north, advanceAt40_north, advanceAt62_north, advanceAt84_north, advanceAt84_south, advanceAt106_north, floorAt18, doorAt18, trapAt18, boxAt18, holeAt18, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt106_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 84) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 84), d1), oracleMember314, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover337 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .south = some outcome) :
    OracleCovered rowCases337 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .south = some (.walk 128) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt128_north, advanceAt128_south, advanceAt150_south, advanceAt172_south, advanceAt194_south, advanceAt216_south, advanceAt238_south, advanceAt260_south, advanceAt282_south, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt282, doorAt282, trapAt282, boxAt282, holeAt282, cornerAt106_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 128) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 128), d1), oracleMember315, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover338 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .east = some outcome) :
    OracleCovered rowCases338 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .east = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_east, advanceAt107_east, advanceAt107_west, advanceAt108_east, advanceAt109_east, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, cornerAt106_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover339 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .west = some outcome) :
    OracleCovered rowCases339 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .west = some (.walk 105) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt88_west, advanceAt89_west, advanceAt90_west, advanceAt91_west, advanceAt92_west, advanceAt93_west, advanceAt94_west, advanceAt95_west, advanceAt96_west, advanceAt97_west, advanceAt98_west, advanceAt99_west, advanceAt100_west, advanceAt101_west, advanceAt102_west, advanceAt103_west, advanceAt104_west, advanceAt105_east, advanceAt105_west, advanceAt106_west, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt106_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 105) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 105), d1), oracleMember317, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover340 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .northEast = some outcome) :
    OracleCovered rowCases340 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .northEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_north, advanceAt106_east, advanceAt106_northEast, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, cornerAt106_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover341 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .northWest = some outcome) :
    OracleCovered rowCases341 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .northWest = some (.walk 83) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_north, advanceAt106_west, advanceAt106_northWest, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt106_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 83) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 83), d1), oracleMember319, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover342 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .southEast = some outcome) :
    OracleCovered rowCases342 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .southEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt106_east, advanceAt106_southEast, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, cornerAt106_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover343 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .southWest = some outcome) :
    OracleCovered rowCases343 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .southWest = some (.walk 127) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt106_west, advanceAt106_southWest, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, cornerAt106_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 127) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 127), d1), oracleMember320, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover344 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .north = some outcome) :
    OracleCovered rowCases344 p outcome := by
  cases h111 : p 111 with
  | false =>
    cases h89 : p 89 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .north = some (.walk 89) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt1_north, advanceAt23_north, advanceAt45_north, advanceAt67_north, advanceAt89_north, advanceAt89_south, advanceAt111_north, floorAt1, doorAt1, trapAt1, boxAt1, holeAt1, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, cornerAt111_north, h89, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 89) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 89), d74075), oracleMember321, same, ?_⟩
      simp only [d57573, d74075, d0, d1, h89, h111, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h67 : p 67 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .north = some (.push 89 (.stay 67)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt1_north, advanceAt23_north, advanceAt45_north, advanceAt67_north, advanceAt89_north, advanceAt89_south, advanceAt111_north, floorAt1, doorAt1, trapAt1, boxAt1, holeAt1, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, cornerAt111_north, h67, h89, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 89 (.stay 67)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 89 (.stay 67)), d67924), oracleMember322, same, ?_⟩
        simp only [d57572, d67923, d67924, d0, d1, h67, h89, h111, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt1_north, advanceAt23_north, advanceAt45_north, advanceAt67_north, advanceAt89_north, advanceAt89_south, advanceAt111_north, floorAt1, doorAt1, trapAt1, boxAt1, holeAt1, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, cornerAt111_north, h67, h89, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt1_north, advanceAt23_north, advanceAt45_north, advanceAt67_north, advanceAt89_north, advanceAt89_south, advanceAt111_north, floorAt1, doorAt1, trapAt1, boxAt1, holeAt1, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, cornerAt111_north, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover345 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .south = some outcome) :
    OracleCovered rowCases345 p outcome := by
  cases h111 : p 111 with
  | false =>
    cases h133 : p 133 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .south = some (.walk 133) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt111_south, advanceAt133_north, advanceAt133_south, advanceAt155_south, advanceAt177_south, advanceAt199_south, advanceAt221_south, advanceAt243_south, advanceAt265_south, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt111_south, h111, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 133) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 133), d82685), oracleMember323, same, ?_⟩
      simp only [d74851, d82685, d0, d1, h111, h133, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h155 : p 155 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .south = some (.push 133 (.stay 155)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt111_south, advanceAt133_north, advanceAt133_south, advanceAt155_south, advanceAt177_south, advanceAt199_south, advanceAt221_south, advanceAt243_south, advanceAt265_south, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt111_south, h111, h133, h155, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 133 (.stay 155)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 133 (.stay 155)), d82690), oracleMember324, same, ?_⟩
        simp only [d82687, d82689, d82690, d0, d1, h111, h133, h155, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt111_south, advanceAt133_north, advanceAt133_south, advanceAt155_south, advanceAt177_south, advanceAt199_south, advanceAt221_south, advanceAt243_south, advanceAt265_south, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt111_south, h111, h133, h155, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt111_south, advanceAt133_north, advanceAt133_south, advanceAt155_south, advanceAt177_south, advanceAt199_south, advanceAt221_south, advanceAt243_south, advanceAt265_south, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt111_south, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover346 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .east = some outcome) :
    OracleCovered rowCases346 p outcome := by
  cases h111 : p 111 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt111_east, advanceAt112_east, advanceAt112_west, advanceAt113_east, advanceAt114_east, advanceAt115_east, advanceAt116_east, advanceAt117_east, advanceAt118_east, advanceAt119_east, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt111_east, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt111_east, advanceAt112_east, advanceAt112_west, advanceAt113_east, advanceAt114_east, advanceAt115_east, advanceAt116_east, advanceAt117_east, advanceAt118_east, advanceAt119_east, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, advanceAt130_east, advanceAt131_east, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt111_east, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover347 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .west = some outcome) :
    OracleCovered rowCases347 p outcome := by
  cases h111 : p 111 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_east, advanceAt110_west, advanceAt111_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, cornerAt111_west, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt110_east, advanceAt110_west, advanceAt111_west, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, cornerAt111_west, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover348 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .northEast = some outcome) :
    OracleCovered rowCases348 p outcome := by
  cases h111 : p 111 with
  | false =>
    cases h89 : p 89 with
    | false =>
      cases h90 : p 90 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .northEast = some (.walk 90) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt111_north, advanceAt111_east, advanceAt111_northEast, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, cornerAt111_northEast, h89, h90, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 90) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 90), d77113), oracleMember325, same, ?_⟩
        simp only [d68221, d68222, d77113, d0, d1, h89, h90, h111, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt111_north, advanceAt111_east, advanceAt111_northEast, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, cornerAt111_northEast, h89, h90, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt111_north, advanceAt111_east, advanceAt111_northEast, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, cornerAt111_northEast, h89, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt111_north, advanceAt111_east, advanceAt111_northEast, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, cornerAt111_northEast, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover349 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .northWest = some outcome) :
    OracleCovered rowCases349 p outcome := by
  cases h111 : p 111 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt111_north, advanceAt111_west, advanceAt111_northWest, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, cornerAt111_northWest, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt111_north, advanceAt111_west, advanceAt111_northWest, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, cornerAt111_northWest, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko22Hazard87
