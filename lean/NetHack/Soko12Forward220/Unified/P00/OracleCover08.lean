import NetHack.Soko12Forward220.Unified.P00.OracleCover07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover96 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .north = some outcome) : OracleCovered rowCases96 p outcome := by
  cases h131 : p 131 with
  | false =>
    cases h105 : p 105 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .north = some (.walk 105) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt1_north, advanceAt27_north, advanceAt53_north, advanceAt79_north, advanceAt105_north, advanceAt105_south, advanceAt131_north, floorAt1, doorAt1, trapAt1, boxAt1, holeAt1, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt131_north, h105, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case052.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case052, memberCase052, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame052.bindings p
      intro binding member
      simp only [frame052, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h105
      · exact h131
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt1_north, advanceAt27_north, advanceAt53_north, advanceAt79_north, advanceAt105_north, advanceAt105_south, advanceAt131_north, floorAt1, doorAt1, trapAt1, boxAt1, holeAt1, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt131_north, h105, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt1_north, advanceAt27_north, advanceAt53_north, advanceAt79_north, advanceAt105_north, advanceAt105_south, advanceAt131_north, floorAt1, doorAt1, trapAt1, boxAt1, holeAt1, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt131_north, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover97 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .south = some outcome) : OracleCovered rowCases97 p outcome := by
  cases h131 : p 131 with
  | false =>
    cases h157 : p 157 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .south = some (.walk 157) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_south, advanceAt157_north, advanceAt157_south, advanceAt183_south, advanceAt209_south, advanceAt235_south, advanceAt261_south, advanceAt287_south, advanceAt313_south, advanceAt339_south, advanceAt365_south, advanceAt391_south, advanceAt417_south, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt417, doorAt417, trapAt417, boxAt417, holeAt417, cornerAt131_south, h131, h157, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case053.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case053, memberCase053, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame053.bindings p
      intro binding member
      simp only [frame053, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h131
      · exact h157
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_south, advanceAt157_north, advanceAt157_south, advanceAt183_south, advanceAt209_south, advanceAt235_south, advanceAt261_south, advanceAt287_south, advanceAt313_south, advanceAt339_south, advanceAt365_south, advanceAt391_south, advanceAt417_south, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt417, doorAt417, trapAt417, boxAt417, holeAt417, cornerAt131_south, h131, h157, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_south, advanceAt157_north, advanceAt157_south, advanceAt183_south, advanceAt209_south, advanceAt235_south, advanceAt261_south, advanceAt287_south, advanceAt313_south, advanceAt339_south, advanceAt365_south, advanceAt391_south, advanceAt417_south, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt417, doorAt417, trapAt417, boxAt417, holeAt417, cornerAt131_south, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover98 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .east = some outcome) : OracleCovered rowCases98 p outcome := by
  cases h131 : p 131 with
  | false =>
    cases h132 : p 132 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .east = some (.walk 132) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_east, advanceAt132_east, advanceAt132_west, advanceAt133_east, advanceAt134_east, advanceAt135_east, advanceAt136_east, advanceAt137_east, advanceAt138_east, advanceAt139_east, advanceAt140_east, advanceAt141_east, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt131_east, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case054.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case054, memberCase054, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame054.bindings p
      intro binding member
      simp only [frame054, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h131
      · exact h132
    | true =>
      cases h133 : p 133 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .east = some (.push 132 (.stay 133)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_east, advanceAt132_east, advanceAt132_west, advanceAt133_east, advanceAt134_east, advanceAt135_east, advanceAt136_east, advanceAt137_east, advanceAt138_east, advanceAt139_east, advanceAt140_east, advanceAt141_east, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt131_east, h131, h132, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case678.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case678, memberCase678, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame678.bindings p
        intro binding member
        simp only [frame678, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h131
        · exact h132
        · exact h133
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_east, advanceAt132_east, advanceAt132_west, advanceAt133_east, advanceAt134_east, advanceAt135_east, advanceAt136_east, advanceAt137_east, advanceAt138_east, advanceAt139_east, advanceAt140_east, advanceAt141_east, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt131_east, h131, h132, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_east, advanceAt132_east, advanceAt132_west, advanceAt133_east, advanceAt134_east, advanceAt135_east, advanceAt136_east, advanceAt137_east, advanceAt138_east, advanceAt139_east, advanceAt140_east, advanceAt141_east, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt131_east, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover99 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .west = some outcome) : OracleCovered rowCases99 p outcome := by
  cases h131 : p 131 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_east, advanceAt130_west, advanceAt131_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt131_west, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_east, advanceAt130_west, advanceAt131_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt131_west, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover100 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .northEast = some outcome) : OracleCovered rowCases100 p outcome := by
  cases h131 : p 131 with
  | false =>
    cases h105 : p 105 with
    | false =>
      cases h106 : p 106 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .northEast = some (.walk 106) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_north, advanceAt131_east, advanceAt131_northEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt131_northEast, h105, h106, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case055.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case055, memberCase055, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame055.bindings p
        intro binding member
        simp only [frame055, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h105
        · exact h106
        · exact h131
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_north, advanceAt131_east, advanceAt131_northEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt131_northEast, h105, h106, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h132 : p 132 with
      | false =>
        cases h106 : p 106 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .northEast = some (.walk 106) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_north, advanceAt131_east, advanceAt131_northEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt131_northEast, h105, h106, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case056.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case056, memberCase056, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame056.bindings p
          intro binding member
          simp only [frame056, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h106
          · exact h131
          · exact h132
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_north, advanceAt131_east, advanceAt131_northEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt131_northEast, h105, h106, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_north, advanceAt131_east, advanceAt131_northEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt131_northEast, h105, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_north, advanceAt131_east, advanceAt131_northEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt131_northEast, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover101 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .northWest = some outcome) : OracleCovered rowCases101 p outcome := by
  cases h131 : p 131 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_north, advanceAt131_west, advanceAt131_northWest, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt131_northWest, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_north, advanceAt131_west, advanceAt131_northWest, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt131_northWest, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover102 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .southEast = some outcome) : OracleCovered rowCases102 p outcome := by
  cases h131 : p 131 with
  | false =>
    cases h157 : p 157 with
    | false =>
      cases h158 : p 158 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .southEast = some (.walk 158) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_south, advanceAt131_east, advanceAt131_southEast, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, cornerAt131_southEast, h131, h157, h158, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case057.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case057, memberCase057, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame057.bindings p
        intro binding member
        simp only [frame057, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h131
        · exact h157
        · exact h158
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_south, advanceAt131_east, advanceAt131_southEast, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, cornerAt131_southEast, h131, h157, h158, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h132 : p 132 with
      | false =>
        cases h158 : p 158 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .southEast = some (.walk 158) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_south, advanceAt131_east, advanceAt131_southEast, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, cornerAt131_southEast, h131, h132, h157, h158, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case058.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case058, memberCase058, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame058.bindings p
          intro binding member
          simp only [frame058, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h131
          · exact h132
          · exact h158
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_south, advanceAt131_east, advanceAt131_southEast, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, cornerAt131_southEast, h131, h132, h157, h158, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_south, advanceAt131_east, advanceAt131_southEast, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, cornerAt131_southEast, h131, h132, h157, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_south, advanceAt131_east, advanceAt131_southEast, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, cornerAt131_southEast, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover103 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .southWest = some outcome) : OracleCovered rowCases103 p outcome := by
  cases h131 : p 131 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_south, advanceAt131_west, advanceAt131_southWest, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, cornerAt131_southWest, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 131 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt131_south, advanceAt131_west, advanceAt131_southWest, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, cornerAt131_southWest, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover104 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .north = some outcome) : OracleCovered rowCases104 p outcome := by
  cases h132 : p 132 with
  | false =>
    cases h106 : p 106 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .north = some (.walk 106) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt106_south, advanceAt132_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt132_north, h106, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case059.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case059, memberCase059, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame059.bindings p
      intro binding member
      simp only [frame059, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h106
      · exact h132
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt106_south, advanceAt132_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt132_north, h106, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt106_south, advanceAt132_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt132_north, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover105 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .south = some outcome) : OracleCovered rowCases105 p outcome := by
  cases h132 : p 132 with
  | false =>
    cases h158 : p 158 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .south = some (.walk 158) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt132_south, advanceAt158_north, advanceAt158_south, advanceAt184_south, advanceAt210_south, advanceAt236_south, advanceAt262_south, advanceAt288_south, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt132_south, h132, h158, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case060.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case060, memberCase060, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame060.bindings p
      intro binding member
      simp only [frame060, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h132
      · exact h158
    | true =>
      cases h184 : p 184 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .south = some (.push 158 (.stay 184)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt132_south, advanceAt158_north, advanceAt158_south, advanceAt184_south, advanceAt210_south, advanceAt236_south, advanceAt262_south, advanceAt288_south, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt132_south, h132, h158, h184, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case697.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case697, memberCase697, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame697.bindings p
        intro binding member
        simp only [frame697, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h132
        · exact h158
        · exact h184
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt132_south, advanceAt158_north, advanceAt158_south, advanceAt184_south, advanceAt210_south, advanceAt236_south, advanceAt262_south, advanceAt288_south, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt132_south, h132, h158, h184, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt132_south, advanceAt158_north, advanceAt158_south, advanceAt184_south, advanceAt210_south, advanceAt236_south, advanceAt262_south, advanceAt288_south, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt132_south, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover106 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .east = some outcome) : OracleCovered rowCases106 p outcome := by
  cases h132 : p 132 with
  | false =>
    cases h133 : p 133 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .east = some (.walk 133) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt132_east, advanceAt133_east, advanceAt133_west, advanceAt134_east, advanceAt135_east, advanceAt136_east, advanceAt137_east, advanceAt138_east, advanceAt139_east, advanceAt140_east, advanceAt141_east, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt132_east, h132, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case061.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case061, memberCase061, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame061.bindings p
      intro binding member
      simp only [frame061, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h132
      · exact h133
    | true =>
      cases h134 : p 134 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .east = some (.push 133 (.stay 134)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt132_east, advanceAt133_east, advanceAt133_west, advanceAt134_east, advanceAt135_east, advanceAt136_east, advanceAt137_east, advanceAt138_east, advanceAt139_east, advanceAt140_east, advanceAt141_east, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt132_east, h132, h133, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case680.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case680, memberCase680, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame680.bindings p
        intro binding member
        simp only [frame680, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h132
        · exact h133
        · exact h134
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt132_east, advanceAt133_east, advanceAt133_west, advanceAt134_east, advanceAt135_east, advanceAt136_east, advanceAt137_east, advanceAt138_east, advanceAt139_east, advanceAt140_east, advanceAt141_east, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt132_east, h132, h133, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt132_east, advanceAt133_east, advanceAt133_west, advanceAt134_east, advanceAt135_east, advanceAt136_east, advanceAt137_east, advanceAt138_east, advanceAt139_east, advanceAt140_east, advanceAt141_east, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt132_east, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover107 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .west = some outcome) : OracleCovered rowCases107 p outcome := by
  cases h132 : p 132 with
  | false =>
    cases h131 : p 131 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .west = some (.walk 131) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_east, advanceAt131_west, advanceAt132_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt132_west, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case062.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case062, memberCase062, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame062.bindings p
      intro binding member
      simp only [frame062, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h131
      · exact h132
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_east, advanceAt131_west, advanceAt132_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt132_west, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 132 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_east, advanceAt131_west, advanceAt132_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt132_west, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P00
