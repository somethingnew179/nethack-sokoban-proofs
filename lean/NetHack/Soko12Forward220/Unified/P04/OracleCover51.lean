import NetHack.Soko12Forward220.Unified.P04.OracleCover50
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover612 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .northEast = some outcome) : OracleCovered rowCases612 p outcome := by
  cases h292 : p 292 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_north, advanceAt292_east, advanceAt292_northEast, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, cornerAt292_northEast, h292, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_north, advanceAt292_east, advanceAt292_northEast, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, cornerAt292_northEast, h292, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover613 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .northWest = some outcome) : OracleCovered rowCases613 p outcome := by
  cases h292 : p 292 with
  | false =>
    cases h291 : p 291 with
    | false =>
      cases h265 : p 265 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .northWest = some (.walk 265) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_north, advanceAt292_west, advanceAt292_northWest, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, cornerAt292_northWest, h265, h291, h292, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case566.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case566, memberCase566, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame566.bindings p
        intro binding member
        simp only [frame566, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h265
        · exact h291
        · exact h292
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_north, advanceAt292_west, advanceAt292_northWest, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, cornerAt292_northWest, h265, h291, h292, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_north, advanceAt292_west, advanceAt292_northWest, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, cornerAt292_northWest, h291, h292, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_north, advanceAt292_west, advanceAt292_northWest, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, cornerAt292_northWest, h292, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover614 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southEast = some outcome) : OracleCovered rowCases614 p outcome := by
  cases h292 : p 292 with
  | false =>
    cases h318 : p 318 with
    | false =>
      cases h319 : p 319 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southEast = some (.walk 319) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_south, advanceAt292_east, advanceAt292_southEast, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt292_southEast, h292, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case567.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case567, memberCase567, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame567.bindings p
        intro binding member
        simp only [frame567, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h292
        · exact h318
        · exact h319
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_south, advanceAt292_east, advanceAt292_southEast, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt292_southEast, h292, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h293 : p 293 with
      | false =>
        cases h319 : p 319 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southEast = some (.walk 319) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_south, advanceAt292_east, advanceAt292_southEast, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt292_southEast, h292, h293, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case568.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case568, memberCase568, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame568.bindings p
          intro binding member
          simp only [frame568, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h292
          · exact h293
          · exact h319
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_south, advanceAt292_east, advanceAt292_southEast, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt292_southEast, h292, h293, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_south, advanceAt292_east, advanceAt292_southEast, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt292_southEast, h292, h293, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_south, advanceAt292_east, advanceAt292_southEast, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt292_southEast, h292, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover615 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southWest = some outcome) : OracleCovered rowCases615 p outcome := by
  cases h292 : p 292 with
  | false =>
    cases h318 : p 318 with
    | false =>
      cases h317 : p 317 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southWest = some (.walk 317) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_south, advanceAt292_west, advanceAt292_southWest, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt292_southWest, h292, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case569.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case569, memberCase569, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame569.bindings p
        intro binding member
        simp only [frame569, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h292
        · exact h317
        · exact h318
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_south, advanceAt292_west, advanceAt292_southWest, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt292_southWest, h292, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h291 : p 291 with
      | false =>
        cases h317 : p 317 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southWest = some (.walk 317) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_south, advanceAt292_west, advanceAt292_southWest, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt292_southWest, h291, h292, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case570.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case570, memberCase570, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame570.bindings p
          intro binding member
          simp only [frame570, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h291
          · exact h292
          · exact h317
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_south, advanceAt292_west, advanceAt292_southWest, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt292_southWest, h291, h292, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_south, advanceAt292_west, advanceAt292_southWest, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt292_southWest, h291, h292, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 292 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt292_south, advanceAt292_west, advanceAt292_southWest, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt292_southWest, h292, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover616 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .north = some outcome) : OracleCovered rowCases616 p outcome := by
  cases h293 : p 293 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt267_south, advanceAt293_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, cornerAt293_north, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt267_south, advanceAt293_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, cornerAt293_north, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover617 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .south = some outcome) : OracleCovered rowCases617 p outcome := by
  cases h293 : p 293 with
  | false =>
    cases h319 : p 319 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .south = some (.walk 319) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt319_north, advanceAt319_south, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt293_south, h293, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case571.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case571, memberCase571, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame571.bindings p
      intro binding member
      simp only [frame571, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h293
      · exact h319
    | true =>
      cases h345 : p 345 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .south = some (.push 319 (.stay 345)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt319_north, advanceAt319_south, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt293_south, h293, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case843.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case843, memberCase843, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame843.bindings p
        intro binding member
        simp only [frame843, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h293
        · exact h319
        · exact h345
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt319_north, advanceAt319_south, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt293_south, h293, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt319_north, advanceAt319_south, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt293_south, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover618 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .east = some outcome) : OracleCovered rowCases618 p outcome := by
  cases h293 : p 293 with
  | false =>
    cases h294 : p 294 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .east = some (.walk 294) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_east, advanceAt294_east, advanceAt294_west, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt293_east, h293, h294, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case572.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case572, memberCase572, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame572.bindings p
      intro binding member
      simp only [frame572, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h293
      · exact h294
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_east, advanceAt294_east, advanceAt294_west, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt293_east, h293, h294, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_east, advanceAt294_east, advanceAt294_west, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt293_east, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover619 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .west = some outcome) : OracleCovered rowCases619 p outcome := by
  cases h293 : p 293 with
  | false =>
    cases h292 : p 292 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .west = some (.walk 292) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_west, advanceAt289_west, advanceAt290_west, advanceAt291_west, advanceAt292_east, advanceAt292_west, advanceAt293_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, cornerAt293_west, h292, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case573.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case573, memberCase573, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame573.bindings p
      intro binding member
      simp only [frame573, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h292
      · exact h293
    | true =>
      cases h291 : p 291 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .west = some (.push 292 (.stay 291)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_west, advanceAt289_west, advanceAt290_west, advanceAt291_west, advanceAt292_east, advanceAt292_west, advanceAt293_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, cornerAt293_west, h291, h292, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case835.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case835, memberCase835, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame835.bindings p
        intro binding member
        simp only [frame835, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h291
        · exact h292
        · exact h293
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_west, advanceAt289_west, advanceAt290_west, advanceAt291_west, advanceAt292_east, advanceAt292_west, advanceAt293_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, cornerAt293_west, h291, h292, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_west, advanceAt289_west, advanceAt290_west, advanceAt291_west, advanceAt292_east, advanceAt292_west, advanceAt293_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, cornerAt293_west, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover620 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .northEast = some outcome) : OracleCovered rowCases620 p outcome := by
  cases h293 : p 293 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_north, advanceAt293_east, advanceAt293_northEast, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, cornerAt293_northEast, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_north, advanceAt293_east, advanceAt293_northEast, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, cornerAt293_northEast, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover621 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .northWest = some outcome) : OracleCovered rowCases621 p outcome := by
  cases h293 : p 293 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_north, advanceAt293_west, advanceAt293_northWest, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, cornerAt293_northWest, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_north, advanceAt293_west, advanceAt293_northWest, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, cornerAt293_northWest, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover622 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southEast = some outcome) : OracleCovered rowCases622 p outcome := by
  cases h293 : p 293 with
  | false =>
    cases h319 : p 319 with
    | false =>
      cases h320 : p 320 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southEast = some (.walk 320) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt293_east, advanceAt293_southEast, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt293_southEast, h293, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case574.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case574, memberCase574, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame574.bindings p
        intro binding member
        simp only [frame574, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h293
        · exact h319
        · exact h320
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt293_east, advanceAt293_southEast, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt293_southEast, h293, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h294 : p 294 with
      | false =>
        cases h320 : p 320 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southEast = some (.walk 320) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt293_east, advanceAt293_southEast, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt293_southEast, h293, h294, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case575.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case575, memberCase575, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame575.bindings p
          intro binding member
          simp only [frame575, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h293
          · exact h294
          · exact h320
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt293_east, advanceAt293_southEast, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt293_southEast, h293, h294, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt293_east, advanceAt293_southEast, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt293_southEast, h293, h294, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt293_east, advanceAt293_southEast, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt293_southEast, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover623 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southWest = some outcome) : OracleCovered rowCases623 p outcome := by
  cases h293 : p 293 with
  | false =>
    cases h319 : p 319 with
    | false =>
      cases h318 : p 318 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southWest = some (.walk 318) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt293_west, advanceAt293_southWest, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt293_southWest, h293, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case576.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case576, memberCase576, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame576.bindings p
        intro binding member
        simp only [frame576, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h293
        · exact h318
        · exact h319
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt293_west, advanceAt293_southWest, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt293_southWest, h293, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h292 : p 292 with
      | false =>
        cases h318 : p 318 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southWest = some (.walk 318) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt293_west, advanceAt293_southWest, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt293_southWest, h292, h293, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case577.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case577, memberCase577, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame577.bindings p
          intro binding member
          simp only [frame577, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h292
          · exact h293
          · exact h318
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt293_west, advanceAt293_southWest, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt293_southWest, h292, h293, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt293_west, advanceAt293_southWest, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt293_southWest, h292, h293, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 293 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt293_south, advanceAt293_west, advanceAt293_southWest, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt293_southWest, h293, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P04
