import NetHack.Soko22Hazard87.OracleCover014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover525 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 145 .northWest = some outcome) :
    OracleCovered rowCases525 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 145 .northWest = some (.walk 122) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt145_north, advanceAt145_west, advanceAt145_northWest, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, cornerAt145_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 122) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 122), d1), oracleMember517, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover526 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 145 .southEast = some outcome) :
    OracleCovered rowCases526 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 145 .southEast = some (.walk 168) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt145_south, advanceAt145_east, advanceAt145_southEast, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt145_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 168) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 168), d1), oracleMember518, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover527 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 145 .southWest = some outcome) :
    OracleCovered rowCases527 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 145 .southWest = some (.walk 166) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt145_south, advanceAt145_west, advanceAt145_southWest, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt145_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 166) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 166), d1), oracleMember519, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover528 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .north = some outcome) :
    OracleCovered rowCases528 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .north = some (.walk 124) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt14_north, advanceAt36_north, advanceAt58_north, advanceAt80_north, advanceAt102_north, advanceAt124_north, advanceAt124_south, advanceAt146_north, floorAt14, doorAt14, trapAt14, boxAt14, holeAt14, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, cornerAt146_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 124) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 124), d1), oracleMember520, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover529 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .south = some outcome) :
    OracleCovered rowCases529 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .south = some (.walk 168) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt146_south, advanceAt168_north, advanceAt168_south, advanceAt190_south, advanceAt212_south, advanceAt234_south, advanceAt256_south, advanceAt278_south, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, cornerAt146_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 168) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 168), d1), oracleMember522, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover530 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .east = some outcome) :
    OracleCovered rowCases530 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .east = some (.walk 147) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt146_east, advanceAt147_east, advanceAt147_west, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, cornerAt146_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 147) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 147), d1), oracleMember524, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover531 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .west = some outcome) :
    OracleCovered rowCases531 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .west = some (.walk 145) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_west, advanceAt140_west, advanceAt141_west, advanceAt142_west, advanceAt143_west, advanceAt144_west, advanceAt145_east, advanceAt145_west, advanceAt146_west, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, cornerAt146_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 145) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 145), d1), oracleMember526, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover532 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .northEast = some outcome) :
    OracleCovered rowCases532 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .northEast = some (.walk 125) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt146_north, advanceAt146_east, advanceAt146_northEast, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, cornerAt146_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 125) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 125), d1), oracleMember528, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover533 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .northWest = some outcome) :
    OracleCovered rowCases533 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .northWest = some (.walk 123) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt146_north, advanceAt146_west, advanceAt146_northWest, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, cornerAt146_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 123) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 123), d1), oracleMember529, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover534 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .southEast = some outcome) :
    OracleCovered rowCases534 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .southEast = some (.walk 169) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt146_south, advanceAt146_east, advanceAt146_southEast, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt146_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 169) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 169), d1), oracleMember530, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover535 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .southWest = some outcome) :
    OracleCovered rowCases535 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 .southWest = some (.walk 167) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt146_south, advanceAt146_west, advanceAt146_southWest, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt146_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 167) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 167), d1), oracleMember531, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover536 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .north = some outcome) :
    OracleCovered rowCases536 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .north = some (.walk 125) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt15_north, advanceAt37_north, advanceAt59_north, advanceAt81_north, advanceAt103_north, advanceAt125_north, advanceAt125_south, advanceAt147_north, floorAt15, doorAt15, trapAt15, boxAt15, holeAt15, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, cornerAt147_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 125) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 125), d1), oracleMember532, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover537 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .south = some outcome) :
    OracleCovered rowCases537 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .south = some (.walk 169) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt147_south, advanceAt169_north, advanceAt169_south, advanceAt191_south, advanceAt213_south, advanceAt235_south, advanceAt257_south, advanceAt279_south, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, cornerAt147_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 169) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 169), d1), oracleMember534, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover538 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .east = some outcome) :
    OracleCovered rowCases538 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .east = some (.walk 148) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt147_east, advanceAt148_east, advanceAt148_west, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, cornerAt147_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 148) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 148), d1), oracleMember536, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover539 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .west = some outcome) :
    OracleCovered rowCases539 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .west = some (.walk 146) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_west, advanceAt140_west, advanceAt141_west, advanceAt142_west, advanceAt143_west, advanceAt144_west, advanceAt145_west, advanceAt146_east, advanceAt146_west, advanceAt147_west, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, cornerAt147_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 146) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 146), d1), oracleMember538, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover540 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .northEast = some outcome) :
    OracleCovered rowCases540 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .northEast = some (.walk 126) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt147_north, advanceAt147_east, advanceAt147_northEast, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, cornerAt147_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 126) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 126), d1), oracleMember540, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover541 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .northWest = some outcome) :
    OracleCovered rowCases541 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .northWest = some (.walk 124) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt147_north, advanceAt147_west, advanceAt147_northWest, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, cornerAt147_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 124) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 124), d1), oracleMember541, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover542 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .southEast = some outcome) :
    OracleCovered rowCases542 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .southEast = some (.walk 170) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt147_south, advanceAt147_east, advanceAt147_southEast, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, cornerAt147_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 170) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 170), d1), oracleMember542, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover543 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .southWest = some outcome) :
    OracleCovered rowCases543 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 .southWest = some (.walk 168) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt147_south, advanceAt147_west, advanceAt147_southWest, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt147_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 168) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 168), d1), oracleMember543, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover544 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .north = some outcome) :
    OracleCovered rowCases544 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .north = some (.walk 126) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt16_north, advanceAt38_north, advanceAt60_north, advanceAt82_north, advanceAt104_north, advanceAt126_north, advanceAt126_south, advanceAt148_north, floorAt16, doorAt16, trapAt16, boxAt16, holeAt16, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, cornerAt148_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 126) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 126), d1), oracleMember544, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover545 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .south = some outcome) :
    OracleCovered rowCases545 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .south = some (.walk 170) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt148_south, advanceAt170_north, advanceAt170_south, advanceAt192_south, advanceAt214_south, advanceAt236_south, advanceAt258_south, advanceAt280_south, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, cornerAt148_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 170) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 170), d1), oracleMember546, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover546 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .east = some outcome) :
    OracleCovered rowCases546 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .east = some (.walk 149) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt148_east, advanceAt149_east, advanceAt149_west, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, cornerAt148_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 149) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 149), d1), oracleMember548, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover547 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .west = some outcome) :
    OracleCovered rowCases547 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .west = some (.walk 147) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_west, advanceAt140_west, advanceAt141_west, advanceAt142_west, advanceAt143_west, advanceAt144_west, advanceAt145_west, advanceAt146_west, advanceAt147_east, advanceAt147_west, advanceAt148_west, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, cornerAt148_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 147) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 147), d1), oracleMember550, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover548 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .northEast = some outcome) :
    OracleCovered rowCases548 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .northEast = some (.walk 127) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt148_north, advanceAt148_east, advanceAt148_northEast, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, cornerAt148_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 127) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 127), d1), oracleMember552, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover549 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .northWest = some outcome) :
    OracleCovered rowCases549 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .northWest = some (.walk 125) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt148_north, advanceAt148_west, advanceAt148_northWest, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, cornerAt148_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 125) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 125), d1), oracleMember553, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover550 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .southEast = some outcome) :
    OracleCovered rowCases550 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .southEast = some (.walk 171) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt148_south, advanceAt148_east, advanceAt148_southEast, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, cornerAt148_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 171) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 171), d1), oracleMember554, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover551 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .southWest = some outcome) :
    OracleCovered rowCases551 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 .southWest = some (.walk 169) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt148_south, advanceAt148_west, advanceAt148_southWest, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, cornerAt148_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 169) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 169), d1), oracleMember555, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover552 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .north = some outcome) :
    OracleCovered rowCases552 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .north = some (.walk 127) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt17_north, advanceAt39_north, advanceAt61_north, advanceAt83_north, advanceAt105_north, advanceAt127_north, advanceAt127_south, advanceAt149_north, floorAt17, doorAt17, trapAt17, boxAt17, holeAt17, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, cornerAt149_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 127) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 127), d1), oracleMember556, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover553 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .south = some outcome) :
    OracleCovered rowCases553 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .south = some (.walk 171) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt149_south, advanceAt171_north, advanceAt171_south, advanceAt193_south, advanceAt215_south, advanceAt237_south, advanceAt259_south, advanceAt281_south, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, cornerAt149_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 171) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 171), d1), oracleMember558, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover554 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .east = some outcome) :
    OracleCovered rowCases554 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .east = some (.walk 150) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt149_east, advanceAt150_east, advanceAt150_west, advanceAt151_east, advanceAt152_east, advanceAt153_east, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, cornerAt149_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 150) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 150), d1), oracleMember560, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover555 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .west = some outcome) :
    OracleCovered rowCases555 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .west = some (.walk 148) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_west, advanceAt140_west, advanceAt141_west, advanceAt142_west, advanceAt143_west, advanceAt144_west, advanceAt145_west, advanceAt146_west, advanceAt147_west, advanceAt148_east, advanceAt148_west, advanceAt149_west, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, cornerAt149_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 148) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 148), d1), oracleMember561, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover556 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .northEast = some outcome) :
    OracleCovered rowCases556 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .northEast = some (.walk 128) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt149_north, advanceAt149_east, advanceAt149_northEast, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, cornerAt149_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 128) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 128), d1), oracleMember563, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover557 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .northWest = some outcome) :
    OracleCovered rowCases557 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .northWest = some (.walk 126) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt149_north, advanceAt149_west, advanceAt149_northWest, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, cornerAt149_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 126) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 126), d1), oracleMember564, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover558 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .southEast = some outcome) :
    OracleCovered rowCases558 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .southEast = some (.walk 172) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt149_south, advanceAt149_east, advanceAt149_southEast, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, cornerAt149_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 172) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 172), d1), oracleMember565, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover559 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .southWest = some outcome) :
    OracleCovered rowCases559 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 .southWest = some (.walk 170) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt149_south, advanceAt149_west, advanceAt149_southWest, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, cornerAt149_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 170) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 170), d1), oracleMember566, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
end NetHack.Soko22Hazard87
