import NetHack.Soko12Forward220.Unified.P04.OracleCover46
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover564 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northEast = some outcome) : OracleCovered rowCases564 p outcome := by
  cases h271 : p 271 with
  | false =>
    cases h245 : p 245 with
    | false =>
      cases h246 : p 246 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northEast = some (.walk 246) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_north, advanceAt271_east, advanceAt271_northEast, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt271_northEast, h245, h246, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case525.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case525, memberCase525, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame525.bindings p
        intro binding member
        simp only [frame525, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h245
        · exact h246
        · exact h271
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_north, advanceAt271_east, advanceAt271_northEast, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt271_northEast, h245, h246, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h272 : p 272 with
      | false =>
        cases h246 : p 246 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northEast = some (.walk 246) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_north, advanceAt271_east, advanceAt271_northEast, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt271_northEast, h245, h246, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case526.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case526, memberCase526, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame526.bindings p
          intro binding member
          simp only [frame526, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h246
          · exact h271
          · exact h272
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_north, advanceAt271_east, advanceAt271_northEast, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt271_northEast, h245, h246, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_north, advanceAt271_east, advanceAt271_northEast, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt271_northEast, h245, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_north, advanceAt271_east, advanceAt271_northEast, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt271_northEast, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover565 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northWest = some outcome) : OracleCovered rowCases565 p outcome := by
  cases h271 : p 271 with
  | false =>
    cases h245 : p 245 with
    | false =>
      cases h244 : p 244 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northWest = some (.walk 244) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_north, advanceAt271_west, advanceAt271_northWest, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt271_northWest, h244, h245, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case527.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case527, memberCase527, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame527.bindings p
        intro binding member
        simp only [frame527, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h244
        · exact h245
        · exact h271
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_north, advanceAt271_west, advanceAt271_northWest, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt271_northWest, h244, h245, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h270 : p 270 with
      | false =>
        cases h244 : p 244 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northWest = some (.walk 244) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_north, advanceAt271_west, advanceAt271_northWest, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt271_northWest, h244, h245, h270, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case528.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case528, memberCase528, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame528.bindings p
          intro binding member
          simp only [frame528, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h244
          · exact h270
          · exact h271
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_north, advanceAt271_west, advanceAt271_northWest, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt271_northWest, h244, h245, h270, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_north, advanceAt271_west, advanceAt271_northWest, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt271_northWest, h245, h270, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_north, advanceAt271_west, advanceAt271_northWest, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt271_northWest, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover566 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .southEast = some outcome) : OracleCovered rowCases566 p outcome := by
  cases h271 : p 271 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_south, advanceAt271_east, advanceAt271_southEast, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt271_southEast, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_south, advanceAt271_east, advanceAt271_southEast, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt271_southEast, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover567 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .southWest = some outcome) : OracleCovered rowCases567 p outcome := by
  cases h271 : p 271 with
  | false =>
    cases h297 : p 297 with
    | false =>
      cases h296 : p 296 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .southWest = some (.walk 296) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_south, advanceAt271_west, advanceAt271_southWest, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt271_southWest, h271, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case529.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case529, memberCase529, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame529.bindings p
        intro binding member
        simp only [frame529, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h271
        · exact h296
        · exact h297
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_south, advanceAt271_west, advanceAt271_southWest, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt271_southWest, h271, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h270 : p 270 with
      | false =>
        cases h296 : p 296 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .southWest = some (.walk 296) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_south, advanceAt271_west, advanceAt271_southWest, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt271_southWest, h270, h271, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case530.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case530, memberCase530, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame530.bindings p
          intro binding member
          simp only [frame530, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h270
          · exact h271
          · exact h296
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_south, advanceAt271_west, advanceAt271_southWest, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt271_southWest, h270, h271, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_south, advanceAt271_west, advanceAt271_southWest, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt271_southWest, h270, h271, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 271 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt271_south, advanceAt271_west, advanceAt271_southWest, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt271_southWest, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover568 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .north = some outcome) : OracleCovered rowCases568 p outcome := by
  cases h272 : p 272 with
  | false =>
    cases h246 : p 246 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .north = some (.walk 246) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt116_north, advanceAt142_north, advanceAt168_north, advanceAt194_north, advanceAt220_north, advanceAt246_north, advanceAt246_south, advanceAt272_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_north, h246, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case531.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case531, memberCase531, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame531.bindings p
      intro binding member
      simp only [frame531, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h246
      · exact h272
    | true =>
      cases h220 : p 220 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .north = some (.push 246 (.stay 220)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt116_north, advanceAt142_north, advanceAt168_north, advanceAt194_north, advanceAt220_north, advanceAt246_north, advanceAt246_south, advanceAt272_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_north, h220, h246, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case806.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case806, memberCase806, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame806.bindings p
        intro binding member
        simp only [frame806, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h220
        · exact h246
        · exact h272
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt116_north, advanceAt142_north, advanceAt168_north, advanceAt194_north, advanceAt220_north, advanceAt246_north, advanceAt246_south, advanceAt272_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_north, h220, h246, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt116_north, advanceAt142_north, advanceAt168_north, advanceAt194_north, advanceAt220_north, advanceAt246_north, advanceAt246_south, advanceAt272_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_north, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover569 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .south = some outcome) : OracleCovered rowCases569 p outcome := by
  cases h272 : p 272 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt298_north, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt272_south, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt298_north, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt272_south, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover570 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .east = some outcome) : OracleCovered rowCases570 p outcome := by
  cases h272 : p 272 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_east, advanceAt273_east, advanceAt273_west, advanceAt274_east, advanceAt275_east, advanceAt276_east, advanceAt277_east, advanceAt278_east, advanceAt279_east, advanceAt280_east, advanceAt281_east, advanceAt282_east, advanceAt283_east, advanceAt284_east, advanceAt285_east, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, floorAt282, doorAt282, trapAt282, boxAt282, holeAt282, floorAt283, doorAt283, trapAt283, boxAt283, holeAt283, floorAt284, doorAt284, trapAt284, boxAt284, holeAt284, floorAt285, doorAt285, trapAt285, boxAt285, holeAt285, cornerAt272_east, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_east, advanceAt273_east, advanceAt273_west, advanceAt274_east, advanceAt275_east, advanceAt276_east, advanceAt277_east, advanceAt278_east, advanceAt279_east, advanceAt280_east, advanceAt281_east, advanceAt282_east, advanceAt283_east, advanceAt284_east, advanceAt285_east, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, floorAt282, doorAt282, trapAt282, boxAt282, holeAt282, floorAt283, doorAt283, trapAt283, boxAt283, holeAt283, floorAt284, doorAt284, trapAt284, boxAt284, holeAt284, floorAt285, doorAt285, trapAt285, boxAt285, holeAt285, cornerAt272_east, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover571 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .west = some outcome) : OracleCovered rowCases571 p outcome := by
  cases h272 : p 272 with
  | false =>
    cases h271 : p 271 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .west = some (.walk 271) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_west, advanceAt264_west, advanceAt265_west, advanceAt266_west, advanceAt267_west, advanceAt268_west, advanceAt269_west, advanceAt270_west, advanceAt271_east, advanceAt271_west, advanceAt272_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_west, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case532.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case532, memberCase532, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame532.bindings p
      intro binding member
      simp only [frame532, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h271
      · exact h272
    | true =>
      cases h270 : p 270 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .west = some (.push 271 (.stay 270)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_west, advanceAt264_west, advanceAt265_west, advanceAt266_west, advanceAt267_west, advanceAt268_west, advanceAt269_west, advanceAt270_west, advanceAt271_east, advanceAt271_west, advanceAt272_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_west, h270, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case825.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case825, memberCase825, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame825.bindings p
        intro binding member
        simp only [frame825, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h270
        · exact h271
        · exact h272
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_west, advanceAt264_west, advanceAt265_west, advanceAt266_west, advanceAt267_west, advanceAt268_west, advanceAt269_west, advanceAt270_west, advanceAt271_east, advanceAt271_west, advanceAt272_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_west, h270, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_west, advanceAt264_west, advanceAt265_west, advanceAt266_west, advanceAt267_west, advanceAt268_west, advanceAt269_west, advanceAt270_west, advanceAt271_east, advanceAt271_west, advanceAt272_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_west, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover572 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .northEast = some outcome) : OracleCovered rowCases572 p outcome := by
  cases h272 : p 272 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_east, advanceAt272_northEast, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt272_northEast, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_east, advanceAt272_northEast, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt272_northEast, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover573 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .northWest = some outcome) : OracleCovered rowCases573 p outcome := by
  cases h272 : p 272 with
  | false =>
    cases h246 : p 246 with
    | false =>
      cases h245 : p 245 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .northWest = some (.walk 245) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_west, advanceAt272_northWest, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_northWest, h245, h246, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case533.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case533, memberCase533, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame533.bindings p
        intro binding member
        simp only [frame533, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h245
        · exact h246
        · exact h272
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_west, advanceAt272_northWest, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_northWest, h245, h246, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h271 : p 271 with
      | false =>
        cases h245 : p 245 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .northWest = some (.walk 245) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_west, advanceAt272_northWest, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_northWest, h245, h246, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case534.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case534, memberCase534, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame534.bindings p
          intro binding member
          simp only [frame534, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h245
          · exact h271
          · exact h272
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_west, advanceAt272_northWest, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_northWest, h245, h246, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_west, advanceAt272_northWest, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_northWest, h246, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_west, advanceAt272_northWest, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_northWest, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover574 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .southEast = some outcome) : OracleCovered rowCases574 p outcome := by
  cases h272 : p 272 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt272_east, advanceAt272_southEast, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, cornerAt272_southEast, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt272_east, advanceAt272_southEast, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, cornerAt272_southEast, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover575 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .southWest = some outcome) : OracleCovered rowCases575 p outcome := by
  cases h272 : p 272 with
  | false =>
    cases h271 : p 271 with
    | false =>
      cases h297 : p 297 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .southWest = some (.walk 297) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt272_west, advanceAt272_southWest, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt272_southWest, h271, h272, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case535.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case535, memberCase535, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame535.bindings p
        intro binding member
        simp only [frame535, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h271
        · exact h272
        · exact h297
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt272_west, advanceAt272_southWest, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt272_southWest, h271, h272, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt272_west, advanceAt272_southWest, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt272_southWest, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 272 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt272_west, advanceAt272_southWest, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt272_southWest, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P04
