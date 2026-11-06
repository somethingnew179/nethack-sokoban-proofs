import NetHack.Soko12Forward220.Unified.P03.OracleCover46
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover564 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .northEast = some outcome) : OracleCovered rowCases564 p outcome := by
  cases h272 : p 272 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_east, advanceAt272_northEast, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt272_northEast, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_east, advanceAt272_northEast, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, cornerAt272_northEast, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover565 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .northWest = some outcome) : OracleCovered rowCases565 p outcome := by
  cases h272 : p 272 with
  | false =>
    cases h246 : p 246 with
    | false =>
      cases h245 : p 245 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .northWest = some (.walk 245) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_west, advanceAt272_northWest, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_northWest, h245, h246, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case531.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case531, memberCase531, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame531.bindings p
        intro binding member
        simp only [frame531, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h245
        · exact h246
        · exact h272
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_west, advanceAt272_northWest, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_northWest, h245, h246, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h271 : p 271 with
      | false =>
        cases h245 : p 245 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .northWest = some (.walk 245) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_west, advanceAt272_northWest, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_northWest, h245, h246, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case532.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case532, memberCase532, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame532.bindings p
          intro binding member
          simp only [frame532, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h245
          · exact h271
          · exact h272
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_west, advanceAt272_northWest, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_northWest, h245, h246, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_west, advanceAt272_northWest, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_northWest, h246, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_north, advanceAt272_west, advanceAt272_northWest, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt272_northWest, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover566 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .southEast = some outcome) : OracleCovered rowCases566 p outcome := by
  cases h272 : p 272 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt272_east, advanceAt272_southEast, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, cornerAt272_southEast, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt272_east, advanceAt272_southEast, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, cornerAt272_southEast, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover567 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .southWest = some outcome) : OracleCovered rowCases567 p outcome := by
  cases h272 : p 272 with
  | false =>
    cases h271 : p 271 with
    | false =>
      cases h297 : p 297 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .southWest = some (.walk 297) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt272_west, advanceAt272_southWest, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt272_southWest, h271, h272, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case533.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case533, memberCase533, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame533.bindings p
        intro binding member
        simp only [frame533, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h271
        · exact h272
        · exact h297
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt272_west, advanceAt272_southWest, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt272_southWest, h271, h272, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt272_west, advanceAt272_southWest, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt272_southWest, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 272 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt272_south, advanceAt272_west, advanceAt272_southWest, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt272_southWest, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover568 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .north = some outcome) : OracleCovered rowCases568 p outcome := by
  cases h288 : p 288 with
  | false =>
    cases h262 : p 262 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .north = some (.walk 262) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt132_north, advanceAt158_north, advanceAt184_north, advanceAt210_north, advanceAt236_north, advanceAt262_north, advanceAt262_south, advanceAt288_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_north, h262, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case534.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case534, memberCase534, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame534.bindings p
      intro binding member
      simp only [frame534, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h262
      · exact h288
    | true =>
      cases h236 : p 236 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .north = some (.push 262 (.stay 236)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt132_north, advanceAt158_north, advanceAt184_north, advanceAt210_north, advanceAt236_north, advanceAt262_north, advanceAt262_south, advanceAt288_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_north, h236, h262, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case806.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case806, memberCase806, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame806.bindings p
        intro binding member
        simp only [frame806, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h236
        · exact h262
        · exact h288
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt132_north, advanceAt158_north, advanceAt184_north, advanceAt210_north, advanceAt236_north, advanceAt262_north, advanceAt262_south, advanceAt288_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_north, h236, h262, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt132_north, advanceAt158_north, advanceAt184_north, advanceAt210_north, advanceAt236_north, advanceAt262_north, advanceAt262_south, advanceAt288_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_north, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover569 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .south = some outcome) : OracleCovered rowCases569 p outcome := by
  cases h288 : p 288 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_south, advanceAt314_north, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt288_south, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_south, advanceAt314_north, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt288_south, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover570 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .east = some outcome) : OracleCovered rowCases570 p outcome := by
  cases h288 : p 288 with
  | false =>
    cases h289 : p 289 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .east = some (.walk 289) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_east, advanceAt289_east, advanceAt289_west, advanceAt290_east, advanceAt291_east, advanceAt292_east, advanceAt293_east, advanceAt294_east, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt288_east, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case535.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case535, memberCase535, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame535.bindings p
      intro binding member
      simp only [frame535, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h288
      · exact h289
    | true =>
      cases h290 : p 290 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .east = some (.push 289 (.stay 290)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_east, advanceAt289_east, advanceAt289_west, advanceAt290_east, advanceAt291_east, advanceAt292_east, advanceAt293_east, advanceAt294_east, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt288_east, h288, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case824.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case824, memberCase824, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame824.bindings p
        intro binding member
        simp only [frame824, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h288
        · exact h289
        · exact h290
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_east, advanceAt289_east, advanceAt289_west, advanceAt290_east, advanceAt291_east, advanceAt292_east, advanceAt293_east, advanceAt294_east, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt288_east, h288, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_east, advanceAt289_east, advanceAt289_west, advanceAt290_east, advanceAt291_east, advanceAt292_east, advanceAt293_east, advanceAt294_east, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt288_east, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover571 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .west = some outcome) : OracleCovered rowCases571 p outcome := by
  cases h288 : p 288 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_east, advanceAt287_west, advanceAt288_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_west, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_east, advanceAt287_west, advanceAt288_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_west, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover572 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .northEast = some outcome) : OracleCovered rowCases572 p outcome := by
  cases h288 : p 288 with
  | false =>
    cases h262 : p 262 with
    | false =>
      cases h263 : p 263 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .northEast = some (.walk 263) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_east, advanceAt288_northEast, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt288_northEast, h262, h263, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case536.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case536, memberCase536, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame536.bindings p
        intro binding member
        simp only [frame536, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h262
        · exact h263
        · exact h288
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_east, advanceAt288_northEast, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt288_northEast, h262, h263, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h289 : p 289 with
      | false =>
        cases h263 : p 263 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .northEast = some (.walk 263) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_east, advanceAt288_northEast, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt288_northEast, h262, h263, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case537.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case537, memberCase537, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame537.bindings p
          intro binding member
          simp only [frame537, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h263
          · exact h288
          · exact h289
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_east, advanceAt288_northEast, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt288_northEast, h262, h263, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_east, advanceAt288_northEast, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt288_northEast, h262, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_east, advanceAt288_northEast, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt288_northEast, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover573 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .northWest = some outcome) : OracleCovered rowCases573 p outcome := by
  cases h288 : p 288 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_west, advanceAt288_northWest, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_northWest, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_west, advanceAt288_northWest, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_northWest, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover574 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .southEast = some outcome) : OracleCovered rowCases574 p outcome := by
  cases h288 : p 288 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_south, advanceAt288_east, advanceAt288_southEast, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, cornerAt288_southEast, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_south, advanceAt288_east, advanceAt288_southEast, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, cornerAt288_southEast, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover575 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .southWest = some outcome) : OracleCovered rowCases575 p outcome := by
  cases h288 : p 288 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_south, advanceAt288_west, advanceAt288_southWest, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, cornerAt288_southWest, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 288 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_south, advanceAt288_west, advanceAt288_southWest, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, cornerAt288_southWest, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P03
