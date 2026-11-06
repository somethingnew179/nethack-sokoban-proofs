import NetHack.Soko12Forward220.Unified.P01.OracleCover04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover60 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .northEast = some outcome) : OracleCovered rowCases60 p outcome := by
  cases h105 : p 105 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_north, advanceAt105_east, advanceAt105_northEast, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt105_northEast, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_north, advanceAt105_east, advanceAt105_northEast, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt105_northEast, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover61 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .northWest = some outcome) : OracleCovered rowCases61 p outcome := by
  cases h105 : p 105 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_north, advanceAt105_west, advanceAt105_northWest, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, cornerAt105_northWest, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_north, advanceAt105_west, advanceAt105_northWest, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, cornerAt105_northWest, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover62 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .southEast = some outcome) : OracleCovered rowCases62 p outcome := by
  cases h105 : p 105 with
  | false =>
    cases h131 : p 131 with
    | false =>
      cases h132 : p 132 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .southEast = some (.walk 132) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt105_east, advanceAt105_southEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt105_southEast, h105, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case027.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case027, memberCase027, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame027.bindings p
        intro binding member
        simp only [frame027, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h105
        · exact h131
        · exact h132
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt105_east, advanceAt105_southEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt105_southEast, h105, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h106 : p 106 with
      | false =>
        cases h132 : p 132 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .southEast = some (.walk 132) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt105_east, advanceAt105_southEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt105_southEast, h105, h106, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case028.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case028, memberCase028, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame028.bindings p
          intro binding member
          simp only [frame028, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h105
          · exact h106
          · exact h132
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt105_east, advanceAt105_southEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt105_southEast, h105, h106, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt105_east, advanceAt105_southEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt105_southEast, h105, h106, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt105_east, advanceAt105_southEast, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt105_southEast, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover63 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .southWest = some outcome) : OracleCovered rowCases63 p outcome := by
  cases h105 : p 105 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt105_west, advanceAt105_southWest, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt105_southWest, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 105 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt105_west, advanceAt105_southWest, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, cornerAt105_southWest, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover64 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .north = some outcome) : OracleCovered rowCases64 p outcome := by
  cases h106 : p 106 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt80_south, advanceAt106_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt106_north, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt80_south, advanceAt106_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt106_north, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover65 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .south = some outcome) : OracleCovered rowCases65 p outcome := by
  cases h106 : p 106 with
  | false =>
    cases h132 : p 132 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .south = some (.walk 132) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt132_north, advanceAt132_south, advanceAt158_south, advanceAt184_south, advanceAt210_south, advanceAt236_south, advanceAt262_south, advanceAt288_south, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt106_south, h106, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case029.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case029, memberCase029, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame029.bindings p
      intro binding member
      simp only [frame029, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h106
      · exact h132
    | true =>
      cases h158 : p 158 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .south = some (.push 132 (.stay 158)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt132_north, advanceAt132_south, advanceAt158_south, advanceAt184_south, advanceAt210_south, advanceAt236_south, advanceAt262_south, advanceAt288_south, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt106_south, h106, h132, h158, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case679.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case679, memberCase679, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame679.bindings p
        intro binding member
        simp only [frame679, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h106
        · exact h132
        · exact h158
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt132_north, advanceAt132_south, advanceAt158_south, advanceAt184_south, advanceAt210_south, advanceAt236_south, advanceAt262_south, advanceAt288_south, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt106_south, h106, h132, h158, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt132_north, advanceAt132_south, advanceAt158_south, advanceAt184_south, advanceAt210_south, advanceAt236_south, advanceAt262_south, advanceAt288_south, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt106_south, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover66 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .east = some outcome) : OracleCovered rowCases66 p outcome := by
  cases h106 : p 106 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_east, advanceAt107_east, advanceAt107_west, advanceAt108_east, advanceAt109_east, advanceAt110_east, advanceAt111_east, advanceAt112_east, advanceAt113_east, advanceAt114_east, advanceAt115_east, advanceAt116_east, advanceAt117_east, advanceAt118_east, advanceAt119_east, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, cornerAt106_east, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_east, advanceAt107_east, advanceAt107_west, advanceAt108_east, advanceAt109_east, advanceAt110_east, advanceAt111_east, advanceAt112_east, advanceAt113_east, advanceAt114_east, advanceAt115_east, advanceAt116_east, advanceAt117_east, advanceAt118_east, advanceAt119_east, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, cornerAt106_east, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover67 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .west = some outcome) : OracleCovered rowCases67 p outcome := by
  cases h106 : p 106 with
  | false =>
    cases h105 : p 105 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .west = some (.walk 105) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_west, advanceAt105_east, advanceAt105_west, advanceAt106_west, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt106_west, h105, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case030.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case030, memberCase030, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame030.bindings p
      intro binding member
      simp only [frame030, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h105
      · exact h106
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_west, advanceAt105_east, advanceAt105_west, advanceAt106_west, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt106_west, h105, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_west, advanceAt105_east, advanceAt105_west, advanceAt106_west, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt106_west, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover68 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .northEast = some outcome) : OracleCovered rowCases68 p outcome := by
  cases h106 : p 106 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_north, advanceAt106_east, advanceAt106_northEast, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, cornerAt106_northEast, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_north, advanceAt106_east, advanceAt106_northEast, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, cornerAt106_northEast, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover69 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .northWest = some outcome) : OracleCovered rowCases69 p outcome := by
  cases h106 : p 106 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_north, advanceAt106_west, advanceAt106_northWest, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt106_northWest, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_north, advanceAt106_west, advanceAt106_northWest, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, cornerAt106_northWest, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover70 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .southEast = some outcome) : OracleCovered rowCases70 p outcome := by
  cases h106 : p 106 with
  | false =>
    cases h132 : p 132 with
    | false =>
      cases h133 : p 133 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .southEast = some (.walk 133) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt106_east, advanceAt106_southEast, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, cornerAt106_southEast, h106, h132, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case031.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case031, memberCase031, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame031.bindings p
        intro binding member
        simp only [frame031, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h106
        · exact h132
        · exact h133
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt106_east, advanceAt106_southEast, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, cornerAt106_southEast, h106, h132, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt106_east, advanceAt106_southEast, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, cornerAt106_southEast, h106, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt106_east, advanceAt106_southEast, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, cornerAt106_southEast, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover71 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .southWest = some outcome) : OracleCovered rowCases71 p outcome := by
  cases h106 : p 106 with
  | false =>
    cases h132 : p 132 with
    | false =>
      cases h131 : p 131 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .southWest = some (.walk 131) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt106_west, advanceAt106_southWest, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt106_southWest, h106, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case032.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case032, memberCase032, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame032.bindings p
        intro binding member
        simp only [frame032, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h106
        · exact h131
        · exact h132
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt106_west, advanceAt106_southWest, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt106_southWest, h106, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h105 : p 105 with
      | false =>
        cases h131 : p 131 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .southWest = some (.walk 131) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt106_west, advanceAt106_southWest, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt106_southWest, h105, h106, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case033.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case033, memberCase033, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame033.bindings p
          intro binding member
          simp only [frame033, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h105
          · exact h106
          · exact h131
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt106_west, advanceAt106_southWest, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt106_southWest, h105, h106, h131, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt106_west, advanceAt106_southWest, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt106_southWest, h105, h106, h132, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 106 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt106_south, advanceAt106_west, advanceAt106_southWest, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, cornerAt106_southWest, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P01
