import NetHack.Soko12Forward220.Unified.P05.OracleCover36
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover444 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northEast = some outcome) : OracleCovered rowCases444 p outcome := by
  cases h219 : p 219 with
  | false =>
    cases h193 : p 193 with
    | false =>
      cases h194 : p 194 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northEast = some (.walk 194) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_north, advanceAt219_east, advanceAt219_northEast, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt219_northEast, h193, h194, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case388.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case388, memberCase388, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame388.bindings p
        intro binding member
        simp only [frame388, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h193
        · exact h194
        · exact h219
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_north, advanceAt219_east, advanceAt219_northEast, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt219_northEast, h193, h194, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h220 : p 220 with
      | false =>
        cases h194 : p 194 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northEast = some (.walk 194) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_north, advanceAt219_east, advanceAt219_northEast, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt219_northEast, h193, h194, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case389.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case389, memberCase389, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame389.bindings p
          intro binding member
          simp only [frame389, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h194
          · exact h219
          · exact h220
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_north, advanceAt219_east, advanceAt219_northEast, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt219_northEast, h193, h194, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_north, advanceAt219_east, advanceAt219_northEast, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt219_northEast, h193, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_north, advanceAt219_east, advanceAt219_northEast, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt219_northEast, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover445 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northWest = some outcome) : OracleCovered rowCases445 p outcome := by
  cases h219 : p 219 with
  | false =>
    cases h193 : p 193 with
    | false =>
      cases h192 : p 192 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northWest = some (.walk 192) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_north, advanceAt219_west, advanceAt219_northWest, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_northWest, h192, h193, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case390.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case390, memberCase390, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame390.bindings p
        intro binding member
        simp only [frame390, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h192
        · exact h193
        · exact h219
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_north, advanceAt219_west, advanceAt219_northWest, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_northWest, h192, h193, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h218 : p 218 with
      | false =>
        cases h192 : p 192 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northWest = some (.walk 192) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_north, advanceAt219_west, advanceAt219_northWest, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_northWest, h192, h193, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case391.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case391, memberCase391, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame391.bindings p
          intro binding member
          simp only [frame391, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h192
          · exact h218
          · exact h219
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_north, advanceAt219_west, advanceAt219_northWest, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_northWest, h192, h193, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_north, advanceAt219_west, advanceAt219_northWest, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_northWest, h193, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_north, advanceAt219_west, advanceAt219_northWest, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_northWest, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover446 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southEast = some outcome) : OracleCovered rowCases446 p outcome := by
  cases h219 : p 219 with
  | false =>
    cases h245 : p 245 with
    | false =>
      cases h246 : p 246 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southEast = some (.walk 246) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt219_east, advanceAt219_southEast, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt219_southEast, h219, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case392.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case392, memberCase392, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame392.bindings p
        intro binding member
        simp only [frame392, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h219
        · exact h245
        · exact h246
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt219_east, advanceAt219_southEast, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt219_southEast, h219, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h220 : p 220 with
      | false =>
        cases h246 : p 246 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southEast = some (.walk 246) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt219_east, advanceAt219_southEast, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt219_southEast, h219, h220, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case393.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case393, memberCase393, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame393.bindings p
          intro binding member
          simp only [frame393, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h219
          · exact h220
          · exact h246
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt219_east, advanceAt219_southEast, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt219_southEast, h219, h220, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt219_east, advanceAt219_southEast, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt219_southEast, h219, h220, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt219_east, advanceAt219_southEast, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt219_southEast, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover447 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southWest = some outcome) : OracleCovered rowCases447 p outcome := by
  cases h219 : p 219 with
  | false =>
    cases h245 : p 245 with
    | false =>
      cases h244 : p 244 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southWest = some (.walk 244) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt219_west, advanceAt219_southWest, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt219_southWest, h219, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case394.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case394, memberCase394, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame394.bindings p
        intro binding member
        simp only [frame394, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h219
        · exact h244
        · exact h245
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt219_west, advanceAt219_southWest, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt219_southWest, h219, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h218 : p 218 with
      | false =>
        cases h244 : p 244 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southWest = some (.walk 244) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt219_west, advanceAt219_southWest, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt219_southWest, h218, h219, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case395.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case395, memberCase395, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame395.bindings p
          intro binding member
          simp only [frame395, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h218
          · exact h219
          · exact h244
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt219_west, advanceAt219_southWest, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt219_southWest, h218, h219, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt219_west, advanceAt219_southWest, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt219_southWest, h218, h219, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 219 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt219_west, advanceAt219_southWest, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt219_southWest, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover448 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .north = some outcome) : OracleCovered rowCases448 p outcome := by
  cases h220 : p 220 with
  | false =>
    cases h194 : p 194 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .north = some (.walk 194) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt116_north, advanceAt142_north, advanceAt168_north, advanceAt194_north, advanceAt194_south, advanceAt220_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_north, h194, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case396.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case396, memberCase396, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame396.bindings p
      intro binding member
      simp only [frame396, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h194
      · exact h220
    | true =>
      cases h168 : p 168 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .north = some (.push 194 (.stay 168)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt116_north, advanceAt142_north, advanceAt168_north, advanceAt194_north, advanceAt194_south, advanceAt220_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_north, h168, h194, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case758.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case758, memberCase758, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame758.bindings p
        intro binding member
        simp only [frame758, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h168
        · exact h194
        · exact h220
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt116_north, advanceAt142_north, advanceAt168_north, advanceAt194_north, advanceAt194_south, advanceAt220_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_north, h168, h194, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt116_north, advanceAt142_north, advanceAt168_north, advanceAt194_north, advanceAt194_south, advanceAt220_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_north, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover449 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .south = some outcome) : OracleCovered rowCases449 p outcome := by
  cases h220 : p 220 with
  | false =>
    cases h246 : p 246 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .south = some (.walk 246) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_south, advanceAt246_north, advanceAt246_south, advanceAt272_south, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt220_south, h220, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case397.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case397, memberCase397, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame397.bindings p
      intro binding member
      simp only [frame397, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h220
      · exact h246
    | true =>
      cases h272 : p 272 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .south = some (.push 246 (.stay 272)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_south, advanceAt246_north, advanceAt246_south, advanceAt272_south, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt220_south, h220, h246, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case809.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case809, memberCase809, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame809.bindings p
        intro binding member
        simp only [frame809, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h220
        · exact h246
        · exact h272
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_south, advanceAt246_north, advanceAt246_south, advanceAt272_south, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt220_south, h220, h246, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_south, advanceAt246_north, advanceAt246_south, advanceAt272_south, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt220_south, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover450 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .east = some outcome) : OracleCovered rowCases450 p outcome := by
  cases h220 : p 220 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_east, advanceAt221_east, advanceAt221_west, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt220_east, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_east, advanceAt221_east, advanceAt221_west, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt220_east, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover451 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .west = some outcome) : OracleCovered rowCases451 p outcome := by
  cases h220 : p 220 with
  | false =>
    cases h219 : p 219 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .west = some (.walk 219) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_west, advanceAt214_west, advanceAt215_west, advanceAt216_west, advanceAt217_west, advanceAt218_west, advanceAt219_east, advanceAt219_west, advanceAt220_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_west, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case398.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case398, memberCase398, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame398.bindings p
      intro binding member
      simp only [frame398, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h219
      · exact h220
    | true =>
      cases h218 : p 218 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .west = some (.push 219 (.stay 218)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_west, advanceAt214_west, advanceAt215_west, advanceAt216_west, advanceAt217_west, advanceAt218_west, advanceAt219_east, advanceAt219_west, advanceAt220_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_west, h218, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case787.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case787, memberCase787, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame787.bindings p
        intro binding member
        simp only [frame787, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h218
        · exact h219
        · exact h220
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_west, advanceAt214_west, advanceAt215_west, advanceAt216_west, advanceAt217_west, advanceAt218_west, advanceAt219_east, advanceAt219_west, advanceAt220_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_west, h218, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_west, advanceAt214_west, advanceAt215_west, advanceAt216_west, advanceAt217_west, advanceAt218_west, advanceAt219_east, advanceAt219_west, advanceAt220_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_west, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover452 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .northEast = some outcome) : OracleCovered rowCases452 p outcome := by
  cases h220 : p 220 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_north, advanceAt220_east, advanceAt220_northEast, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, cornerAt220_northEast, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_north, advanceAt220_east, advanceAt220_northEast, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, cornerAt220_northEast, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover453 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .northWest = some outcome) : OracleCovered rowCases453 p outcome := by
  cases h220 : p 220 with
  | false =>
    cases h194 : p 194 with
    | false =>
      cases h193 : p 193 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .northWest = some (.walk 193) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_north, advanceAt220_west, advanceAt220_northWest, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_northWest, h193, h194, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case399.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case399, memberCase399, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame399.bindings p
        intro binding member
        simp only [frame399, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h193
        · exact h194
        · exact h220
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_north, advanceAt220_west, advanceAt220_northWest, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_northWest, h193, h194, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h219 : p 219 with
      | false =>
        cases h193 : p 193 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .northWest = some (.walk 193) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_north, advanceAt220_west, advanceAt220_northWest, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_northWest, h193, h194, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case400.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case400, memberCase400, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame400.bindings p
          intro binding member
          simp only [frame400, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h193
          · exact h219
          · exact h220
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_north, advanceAt220_west, advanceAt220_northWest, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_northWest, h193, h194, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_north, advanceAt220_west, advanceAt220_northWest, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_northWest, h194, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_north, advanceAt220_west, advanceAt220_northWest, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, cornerAt220_northWest, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover454 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .southEast = some outcome) : OracleCovered rowCases454 p outcome := by
  cases h220 : p 220 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_south, advanceAt220_east, advanceAt220_southEast, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt220_southEast, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_south, advanceAt220_east, advanceAt220_southEast, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, cornerAt220_southEast, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover455 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .southWest = some outcome) : OracleCovered rowCases455 p outcome := by
  cases h220 : p 220 with
  | false =>
    cases h246 : p 246 with
    | false =>
      cases h245 : p 245 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .southWest = some (.walk 245) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_south, advanceAt220_west, advanceAt220_southWest, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt220_southWest, h220, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case401.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case401, memberCase401, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame401.bindings p
        intro binding member
        simp only [frame401, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h220
        · exact h245
        · exact h246
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_south, advanceAt220_west, advanceAt220_southWest, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt220_southWest, h220, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h219 : p 219 with
      | false =>
        cases h245 : p 245 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .southWest = some (.walk 245) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_south, advanceAt220_west, advanceAt220_southWest, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt220_southWest, h219, h220, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case402.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case402, memberCase402, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame402.bindings p
          intro binding member
          simp only [frame402, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h219
          · exact h220
          · exact h245
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_south, advanceAt220_west, advanceAt220_southWest, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt220_southWest, h219, h220, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_south, advanceAt220_west, advanceAt220_southWest, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt220_southWest, h219, h220, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 220 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt220_south, advanceAt220_west, advanceAt220_southWest, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, cornerAt220_southWest, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P05
