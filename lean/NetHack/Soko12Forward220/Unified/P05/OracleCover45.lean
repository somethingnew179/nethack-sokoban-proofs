import NetHack.Soko12Forward220.Unified.P05.OracleCover44
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover540 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northEast = some outcome) : OracleCovered rowCases540 p outcome := by
  cases h263 : p 263 with
  | false =>
    cases h237 : p 237 with
    | false =>
      cases h238 : p 238 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northEast = some (.walk 238) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_north, advanceAt263_east, advanceAt263_northEast, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt263_northEast, h237, h238, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case488.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case488, memberCase488, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame488.bindings p
        intro binding member
        simp only [frame488, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h237
        · exact h238
        · exact h263
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_north, advanceAt263_east, advanceAt263_northEast, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt263_northEast, h237, h238, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h264 : p 264 with
      | false =>
        cases h238 : p 238 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northEast = some (.walk 238) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_north, advanceAt263_east, advanceAt263_northEast, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt263_northEast, h237, h238, h263, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case489.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case489, memberCase489, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame489.bindings p
          intro binding member
          simp only [frame489, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h238
          · exact h263
          · exact h264
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_north, advanceAt263_east, advanceAt263_northEast, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt263_northEast, h237, h238, h263, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_north, advanceAt263_east, advanceAt263_northEast, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt263_northEast, h237, h263, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_north, advanceAt263_east, advanceAt263_northEast, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt263_northEast, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover541 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northWest = some outcome) : OracleCovered rowCases541 p outcome := by
  cases h263 : p 263 with
  | false =>
    cases h237 : p 237 with
    | false =>
      cases h236 : p 236 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northWest = some (.walk 236) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_north, advanceAt263_west, advanceAt263_northWest, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt263_northWest, h236, h237, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case490.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case490, memberCase490, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame490.bindings p
        intro binding member
        simp only [frame490, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h236
        · exact h237
        · exact h263
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_north, advanceAt263_west, advanceAt263_northWest, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt263_northWest, h236, h237, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h262 : p 262 with
      | false =>
        cases h236 : p 236 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northWest = some (.walk 236) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_north, advanceAt263_west, advanceAt263_northWest, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt263_northWest, h236, h237, h262, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case491.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case491, memberCase491, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame491.bindings p
          intro binding member
          simp only [frame491, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h236
          · exact h262
          · exact h263
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_north, advanceAt263_west, advanceAt263_northWest, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt263_northWest, h236, h237, h262, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_north, advanceAt263_west, advanceAt263_northWest, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt263_northWest, h237, h262, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_north, advanceAt263_west, advanceAt263_northWest, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, cornerAt263_northWest, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover542 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southEast = some outcome) : OracleCovered rowCases542 p outcome := by
  cases h263 : p 263 with
  | false =>
    cases h289 : p 289 with
    | false =>
      cases h290 : p 290 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southEast = some (.walk 290) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_south, advanceAt263_east, advanceAt263_southEast, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, cornerAt263_southEast, h263, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case492.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case492, memberCase492, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame492.bindings p
        intro binding member
        simp only [frame492, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h263
        · exact h289
        · exact h290
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_south, advanceAt263_east, advanceAt263_southEast, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, cornerAt263_southEast, h263, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h264 : p 264 with
      | false =>
        cases h290 : p 290 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southEast = some (.walk 290) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_south, advanceAt263_east, advanceAt263_southEast, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, cornerAt263_southEast, h263, h264, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case493.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case493, memberCase493, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame493.bindings p
          intro binding member
          simp only [frame493, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h263
          · exact h264
          · exact h290
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_south, advanceAt263_east, advanceAt263_southEast, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, cornerAt263_southEast, h263, h264, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_south, advanceAt263_east, advanceAt263_southEast, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, cornerAt263_southEast, h263, h264, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_south, advanceAt263_east, advanceAt263_southEast, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, cornerAt263_southEast, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover543 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southWest = some outcome) : OracleCovered rowCases543 p outcome := by
  cases h263 : p 263 with
  | false =>
    cases h289 : p 289 with
    | false =>
      cases h288 : p 288 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southWest = some (.walk 288) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_south, advanceAt263_west, advanceAt263_southWest, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt263_southWest, h263, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case494.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case494, memberCase494, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame494.bindings p
        intro binding member
        simp only [frame494, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h263
        · exact h288
        · exact h289
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_south, advanceAt263_west, advanceAt263_southWest, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt263_southWest, h263, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h262 : p 262 with
      | false =>
        cases h288 : p 288 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southWest = some (.walk 288) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_south, advanceAt263_west, advanceAt263_southWest, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt263_southWest, h262, h263, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case495.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case495, memberCase495, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame495.bindings p
          intro binding member
          simp only [frame495, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h262
          · exact h263
          · exact h288
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_south, advanceAt263_west, advanceAt263_southWest, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt263_southWest, h262, h263, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_south, advanceAt263_west, advanceAt263_southWest, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt263_southWest, h262, h263, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 263 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt263_south, advanceAt263_west, advanceAt263_southWest, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt263_southWest, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover544 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .north = some outcome) : OracleCovered rowCases544 p outcome := by
  cases h264 : p 264 with
  | false =>
    cases h238 : p 238 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .north = some (.walk 238) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt160_north, advanceAt186_north, advanceAt212_north, advanceAt238_north, advanceAt238_south, advanceAt264_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_north, h238, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case496.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case496, memberCase496, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame496.bindings p
      intro binding member
      simp only [frame496, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h238
      · exact h264
    | true =>
      cases h212 : p 212 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .north = some (.push 238 (.stay 212)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt160_north, advanceAt186_north, advanceAt212_north, advanceAt238_north, advanceAt238_south, advanceAt264_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_north, h212, h238, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case796.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case796, memberCase796, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame796.bindings p
        intro binding member
        simp only [frame796, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h212
        · exact h238
        · exact h264
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt160_north, advanceAt186_north, advanceAt212_north, advanceAt238_north, advanceAt238_south, advanceAt264_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_north, h212, h238, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt160_north, advanceAt186_north, advanceAt212_north, advanceAt238_north, advanceAt238_south, advanceAt264_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_north, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover545 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .south = some outcome) : OracleCovered rowCases545 p outcome := by
  cases h264 : p 264 with
  | false =>
    cases h290 : p 290 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .south = some (.walk 290) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt290_north, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt264_south, h264, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case497.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case497, memberCase497, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame497.bindings p
      intro binding member
      simp only [frame497, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h264
      · exact h290
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt290_north, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt264_south, h264, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt290_north, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt264_south, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover546 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .east = some outcome) : OracleCovered rowCases546 p outcome := by
  cases h264 : p 264 with
  | false =>
    cases h265 : p 265 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .east = some (.walk 265) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_east, advanceAt265_east, advanceAt265_west, advanceAt266_east, advanceAt267_east, advanceAt268_east, advanceAt269_east, advanceAt270_east, advanceAt271_east, advanceAt272_east, advanceAt273_east, advanceAt274_east, advanceAt275_east, advanceAt276_east, advanceAt277_east, advanceAt278_east, advanceAt279_east, advanceAt280_east, advanceAt281_east, advanceAt282_east, advanceAt283_east, advanceAt284_east, advanceAt285_east, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, floorAt282, doorAt282, trapAt282, boxAt282, holeAt282, floorAt283, doorAt283, trapAt283, boxAt283, holeAt283, floorAt284, doorAt284, trapAt284, boxAt284, holeAt284, floorAt285, doorAt285, trapAt285, boxAt285, holeAt285, cornerAt264_east, h264, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case498.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case498, memberCase498, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame498.bindings p
      intro binding member
      simp only [frame498, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h264
      · exact h265
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_east, advanceAt265_east, advanceAt265_west, advanceAt266_east, advanceAt267_east, advanceAt268_east, advanceAt269_east, advanceAt270_east, advanceAt271_east, advanceAt272_east, advanceAt273_east, advanceAt274_east, advanceAt275_east, advanceAt276_east, advanceAt277_east, advanceAt278_east, advanceAt279_east, advanceAt280_east, advanceAt281_east, advanceAt282_east, advanceAt283_east, advanceAt284_east, advanceAt285_east, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, floorAt282, doorAt282, trapAt282, boxAt282, holeAt282, floorAt283, doorAt283, trapAt283, boxAt283, holeAt283, floorAt284, doorAt284, trapAt284, boxAt284, holeAt284, floorAt285, doorAt285, trapAt285, boxAt285, holeAt285, cornerAt264_east, h264, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_east, advanceAt265_east, advanceAt265_west, advanceAt266_east, advanceAt267_east, advanceAt268_east, advanceAt269_east, advanceAt270_east, advanceAt271_east, advanceAt272_east, advanceAt273_east, advanceAt274_east, advanceAt275_east, advanceAt276_east, advanceAt277_east, advanceAt278_east, advanceAt279_east, advanceAt280_east, advanceAt281_east, advanceAt282_east, advanceAt283_east, advanceAt284_east, advanceAt285_east, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, floorAt282, doorAt282, trapAt282, boxAt282, holeAt282, floorAt283, doorAt283, trapAt283, boxAt283, holeAt283, floorAt284, doorAt284, trapAt284, boxAt284, holeAt284, floorAt285, doorAt285, trapAt285, boxAt285, holeAt285, cornerAt264_east, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover547 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .west = some outcome) : OracleCovered rowCases547 p outcome := by
  cases h264 : p 264 with
  | false =>
    cases h263 : p 263 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .west = some (.walk 263) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_east, advanceAt263_west, advanceAt264_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_west, h263, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case499.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case499, memberCase499, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame499.bindings p
      intro binding member
      simp only [frame499, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h263
      · exact h264
    | true =>
      cases h262 : p 262 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .west = some (.push 263 (.stay 262)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_east, advanceAt263_west, advanceAt264_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_west, h262, h263, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case815.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case815, memberCase815, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame815.bindings p
        intro binding member
        simp only [frame815, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h262
        · exact h263
        · exact h264
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_east, advanceAt263_west, advanceAt264_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_west, h262, h263, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_east, advanceAt263_west, advanceAt264_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_west, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover548 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northEast = some outcome) : OracleCovered rowCases548 p outcome := by
  cases h264 : p 264 with
  | false =>
    cases h238 : p 238 with
    | false =>
      cases h239 : p 239 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northEast = some (.walk 239) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_north, advanceAt264_east, advanceAt264_northEast, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt264_northEast, h238, h239, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case500.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case500, memberCase500, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame500.bindings p
        intro binding member
        simp only [frame500, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h238
        · exact h239
        · exact h264
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_north, advanceAt264_east, advanceAt264_northEast, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt264_northEast, h238, h239, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h265 : p 265 with
      | false =>
        cases h239 : p 239 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northEast = some (.walk 239) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_north, advanceAt264_east, advanceAt264_northEast, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt264_northEast, h238, h239, h264, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case501.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case501, memberCase501, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame501.bindings p
          intro binding member
          simp only [frame501, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h239
          · exact h264
          · exact h265
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_north, advanceAt264_east, advanceAt264_northEast, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt264_northEast, h238, h239, h264, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_north, advanceAt264_east, advanceAt264_northEast, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt264_northEast, h238, h264, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_north, advanceAt264_east, advanceAt264_northEast, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt264_northEast, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover549 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northWest = some outcome) : OracleCovered rowCases549 p outcome := by
  cases h264 : p 264 with
  | false =>
    cases h238 : p 238 with
    | false =>
      cases h237 : p 237 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northWest = some (.walk 237) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_north, advanceAt264_west, advanceAt264_northWest, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_northWest, h237, h238, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case502.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case502, memberCase502, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame502.bindings p
        intro binding member
        simp only [frame502, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h237
        · exact h238
        · exact h264
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_north, advanceAt264_west, advanceAt264_northWest, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_northWest, h237, h238, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h263 : p 263 with
      | false =>
        cases h237 : p 237 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northWest = some (.walk 237) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_north, advanceAt264_west, advanceAt264_northWest, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_northWest, h237, h238, h263, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case503.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case503, memberCase503, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame503.bindings p
          intro binding member
          simp only [frame503, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h237
          · exact h263
          · exact h264
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_north, advanceAt264_west, advanceAt264_northWest, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_northWest, h237, h238, h263, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_north, advanceAt264_west, advanceAt264_northWest, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_northWest, h238, h263, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_north, advanceAt264_west, advanceAt264_northWest, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, cornerAt264_northWest, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover550 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southEast = some outcome) : OracleCovered rowCases550 p outcome := by
  cases h264 : p 264 with
  | false =>
    cases h290 : p 290 with
    | false =>
      cases h291 : p 291 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southEast = some (.walk 291) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt264_east, advanceAt264_southEast, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, cornerAt264_southEast, h264, h290, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case504.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case504, memberCase504, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame504.bindings p
        intro binding member
        simp only [frame504, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h264
        · exact h290
        · exact h291
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt264_east, advanceAt264_southEast, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, cornerAt264_southEast, h264, h290, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h265 : p 265 with
      | false =>
        cases h291 : p 291 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southEast = some (.walk 291) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt264_east, advanceAt264_southEast, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, cornerAt264_southEast, h264, h265, h290, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case505.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case505, memberCase505, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame505.bindings p
          intro binding member
          simp only [frame505, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h264
          · exact h265
          · exact h291
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt264_east, advanceAt264_southEast, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, cornerAt264_southEast, h264, h265, h290, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt264_east, advanceAt264_southEast, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, cornerAt264_southEast, h264, h265, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt264_east, advanceAt264_southEast, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, cornerAt264_southEast, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover551 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southWest = some outcome) : OracleCovered rowCases551 p outcome := by
  cases h264 : p 264 with
  | false =>
    cases h290 : p 290 with
    | false =>
      cases h289 : p 289 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southWest = some (.walk 289) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt264_west, advanceAt264_southWest, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, cornerAt264_southWest, h264, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case506.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case506, memberCase506, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame506.bindings p
        intro binding member
        simp only [frame506, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h264
        · exact h289
        · exact h290
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt264_west, advanceAt264_southWest, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, cornerAt264_southWest, h264, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h263 : p 263 with
      | false =>
        cases h289 : p 289 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southWest = some (.walk 289) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt264_west, advanceAt264_southWest, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, cornerAt264_southWest, h263, h264, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case507.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case507, memberCase507, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame507.bindings p
          intro binding member
          simp only [frame507, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h263
          · exact h264
          · exact h289
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt264_west, advanceAt264_southWest, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, cornerAt264_southWest, h263, h264, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt264_west, advanceAt264_southWest, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, cornerAt264_southWest, h263, h264, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 264 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt264_south, advanceAt264_west, advanceAt264_southWest, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, cornerAt264_southWest, h264, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P05
