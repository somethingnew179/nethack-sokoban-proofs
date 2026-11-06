import NetHack.Soko12Forward220.Unified.P01.OracleCover37
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover456 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .north = some outcome) : OracleCovered rowCases456 p outcome := by
  cases h241 : p 241 with
  | false =>
    cases h215 : p 215 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .north = some (.walk 215) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt215_south, advanceAt241_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt241_north, h215, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case434.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case434, memberCase434, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame434.bindings p
      intro binding member
      simp only [frame434, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h215
      · exact h241
    | true =>
      cases h189 : p 189 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .north = some (.push 215 (.stay 189)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt215_south, advanceAt241_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt241_north, h189, h215, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case768.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case768, memberCase768, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame768.bindings p
        intro binding member
        simp only [frame768, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h189
        · exact h215
        · exact h241
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt215_south, advanceAt241_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt241_north, h189, h215, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt215_south, advanceAt241_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt241_north, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover457 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .south = some outcome) : OracleCovered rowCases457 p outcome := by
  cases h241 : p 241 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_south, advanceAt267_north, advanceAt267_south, advanceAt293_south, advanceAt319_south, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt241_south, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_south, advanceAt267_north, advanceAt267_south, advanceAt293_south, advanceAt319_south, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt241_south, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover458 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .east = some outcome) : OracleCovered rowCases458 p outcome := by
  cases h241 : p 241 with
  | false =>
    cases h242 : p 242 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .east = some (.walk 242) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_east, advanceAt242_east, advanceAt242_west, advanceAt243_east, advanceAt244_east, advanceAt245_east, advanceAt246_east, advanceAt247_east, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, cornerAt241_east, h241, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case435.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case435, memberCase435, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame435.bindings p
      intro binding member
      simp only [frame435, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h241
      · exact h242
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_east, advanceAt242_east, advanceAt242_west, advanceAt243_east, advanceAt244_east, advanceAt245_east, advanceAt246_east, advanceAt247_east, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, cornerAt241_east, h241, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_east, advanceAt242_east, advanceAt242_west, advanceAt243_east, advanceAt244_east, advanceAt245_east, advanceAt246_east, advanceAt247_east, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, cornerAt241_east, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover459 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .west = some outcome) : OracleCovered rowCases459 p outcome := by
  cases h241 : p 241 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt234_west, advanceAt235_west, advanceAt236_west, advanceAt237_west, advanceAt238_west, advanceAt239_west, advanceAt240_east, advanceAt240_west, advanceAt241_west, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt241_west, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt234_west, advanceAt235_west, advanceAt236_west, advanceAt237_west, advanceAt238_west, advanceAt239_west, advanceAt240_east, advanceAt240_west, advanceAt241_west, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt241_west, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover460 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .northEast = some outcome) : OracleCovered rowCases460 p outcome := by
  cases h241 : p 241 with
  | false =>
    cases h215 : p 215 with
    | false =>
      cases h216 : p 216 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .northEast = some (.walk 216) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_north, advanceAt241_east, advanceAt241_northEast, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt241_northEast, h215, h216, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case436.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case436, memberCase436, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame436.bindings p
        intro binding member
        simp only [frame436, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h215
        · exact h216
        · exact h241
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_north, advanceAt241_east, advanceAt241_northEast, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt241_northEast, h215, h216, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h242 : p 242 with
      | false =>
        cases h216 : p 216 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .northEast = some (.walk 216) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_north, advanceAt241_east, advanceAt241_northEast, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt241_northEast, h215, h216, h241, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case437.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case437, memberCase437, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame437.bindings p
          intro binding member
          simp only [frame437, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h216
          · exact h241
          · exact h242
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_north, advanceAt241_east, advanceAt241_northEast, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt241_northEast, h215, h216, h241, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_north, advanceAt241_east, advanceAt241_northEast, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt241_northEast, h215, h241, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_north, advanceAt241_east, advanceAt241_northEast, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt241_northEast, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover461 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .northWest = some outcome) : OracleCovered rowCases461 p outcome := by
  cases h241 : p 241 with
  | false =>
    cases h215 : p 215 with
    | false =>
      cases h214 : p 214 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .northWest = some (.walk 214) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_north, advanceAt241_west, advanceAt241_northWest, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt241_northWest, h214, h215, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case438.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case438, memberCase438, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame438.bindings p
        intro binding member
        simp only [frame438, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h214
        · exact h215
        · exact h241
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_north, advanceAt241_west, advanceAt241_northWest, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt241_northWest, h214, h215, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_north, advanceAt241_west, advanceAt241_northWest, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt241_northWest, h215, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_north, advanceAt241_west, advanceAt241_northWest, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt241_northWest, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover462 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .southEast = some outcome) : OracleCovered rowCases462 p outcome := by
  cases h241 : p 241 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_south, advanceAt241_east, advanceAt241_southEast, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt241_southEast, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_south, advanceAt241_east, advanceAt241_southEast, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt241_southEast, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover463 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .southWest = some outcome) : OracleCovered rowCases463 p outcome := by
  cases h241 : p 241 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_south, advanceAt241_west, advanceAt241_southWest, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt241_southWest, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 241 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt241_south, advanceAt241_west, advanceAt241_southWest, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt241_southWest, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover464 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .north = some outcome) : OracleCovered rowCases464 p outcome := by
  cases h242 : p 242 with
  | false =>
    cases h216 : p 216 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .north = some (.walk 216) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt164_north, advanceAt190_north, advanceAt216_north, advanceAt216_south, advanceAt242_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt242_north, h216, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case439.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case439, memberCase439, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame439.bindings p
      intro binding member
      simp only [frame439, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h216
      · exact h242
    | true =>
      cases h190 : p 190 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .north = some (.push 216 (.stay 190)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt164_north, advanceAt190_north, advanceAt216_north, advanceAt216_south, advanceAt242_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt242_north, h190, h216, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case772.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case772, memberCase772, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame772.bindings p
        intro binding member
        simp only [frame772, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h190
        · exact h216
        · exact h242
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt164_north, advanceAt190_north, advanceAt216_north, advanceAt216_south, advanceAt242_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt242_north, h190, h216, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt164_north, advanceAt190_north, advanceAt216_north, advanceAt216_south, advanceAt242_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt242_north, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover465 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .south = some outcome) : OracleCovered rowCases465 p outcome := by
  cases h242 : p 242 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_south, advanceAt268_north, advanceAt268_south, advanceAt294_south, advanceAt320_south, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt242_south, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_south, advanceAt268_north, advanceAt268_south, advanceAt294_south, advanceAt320_south, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt242_south, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover466 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .east = some outcome) : OracleCovered rowCases466 p outcome := by
  cases h242 : p 242 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_east, advanceAt243_east, advanceAt243_west, advanceAt244_east, advanceAt245_east, advanceAt246_east, advanceAt247_east, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, cornerAt242_east, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt242_east, advanceAt243_east, advanceAt243_west, advanceAt244_east, advanceAt245_east, advanceAt246_east, advanceAt247_east, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, cornerAt242_east, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover467 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .west = some outcome) : OracleCovered rowCases467 p outcome := by
  cases h242 : p 242 with
  | false =>
    cases h241 : p 241 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .west = some (.walk 241) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt234_west, advanceAt235_west, advanceAt236_west, advanceAt237_west, advanceAt238_west, advanceAt239_west, advanceAt240_west, advanceAt241_east, advanceAt241_west, advanceAt242_west, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt242_west, h241, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case440.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case440, memberCase440, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame440.bindings p
      intro binding member
      simp only [frame440, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h241
      · exact h242
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt234_west, advanceAt235_west, advanceAt236_west, advanceAt237_west, advanceAt238_west, advanceAt239_west, advanceAt240_west, advanceAt241_east, advanceAt241_west, advanceAt242_west, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt242_west, h241, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 242 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt234_west, advanceAt235_west, advanceAt236_west, advanceAt237_west, advanceAt238_west, advanceAt239_west, advanceAt240_west, advanceAt241_east, advanceAt241_west, advanceAt242_west, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt242_west, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P01
