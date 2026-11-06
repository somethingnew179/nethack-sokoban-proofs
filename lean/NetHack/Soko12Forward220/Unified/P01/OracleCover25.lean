import NetHack.Soko12Forward220.Unified.P01.OracleCover24
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover300 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .northEast = some outcome) : OracleCovered rowCases300 p outcome := by
  cases h189 : p 189 with
  | false =>
    cases h163 : p 163 with
    | false =>
      cases h164 : p 164 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .northEast = some (.walk 164) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_north, advanceAt189_east, advanceAt189_northEast, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt189_northEast, h163, h164, h189, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case260.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case260, memberCase260, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame260.bindings p
        intro binding member
        simp only [frame260, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h163
        · exact h164
        · exact h189
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_north, advanceAt189_east, advanceAt189_northEast, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt189_northEast, h163, h164, h189, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h190 : p 190 with
      | false =>
        cases h164 : p 164 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .northEast = some (.walk 164) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_north, advanceAt189_east, advanceAt189_northEast, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt189_northEast, h163, h164, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case261.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case261, memberCase261, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame261.bindings p
          intro binding member
          simp only [frame261, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h164
          · exact h189
          · exact h190
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_north, advanceAt189_east, advanceAt189_northEast, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt189_northEast, h163, h164, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_north, advanceAt189_east, advanceAt189_northEast, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt189_northEast, h163, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_north, advanceAt189_east, advanceAt189_northEast, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt189_northEast, h189, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover301 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .northWest = some outcome) : OracleCovered rowCases301 p outcome := by
  cases h189 : p 189 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_north, advanceAt189_west, advanceAt189_northWest, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, cornerAt189_northWest, h189, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_north, advanceAt189_west, advanceAt189_northWest, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, cornerAt189_northWest, h189, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover302 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .southEast = some outcome) : OracleCovered rowCases302 p outcome := by
  cases h189 : p 189 with
  | false =>
    cases h215 : p 215 with
    | false =>
      cases h216 : p 216 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .southEast = some (.walk 216) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_south, advanceAt189_east, advanceAt189_southEast, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt189_southEast, h189, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case262.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case262, memberCase262, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame262.bindings p
        intro binding member
        simp only [frame262, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h189
        · exact h215
        · exact h216
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_south, advanceAt189_east, advanceAt189_southEast, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt189_southEast, h189, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h190 : p 190 with
      | false =>
        cases h216 : p 216 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .southEast = some (.walk 216) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_south, advanceAt189_east, advanceAt189_southEast, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt189_southEast, h189, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case263.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case263, memberCase263, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame263.bindings p
          intro binding member
          simp only [frame263, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h189
          · exact h190
          · exact h216
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_south, advanceAt189_east, advanceAt189_southEast, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt189_southEast, h189, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_south, advanceAt189_east, advanceAt189_southEast, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt189_southEast, h189, h190, h215, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_south, advanceAt189_east, advanceAt189_southEast, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt189_southEast, h189, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover303 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .southWest = some outcome) : OracleCovered rowCases303 p outcome := by
  cases h189 : p 189 with
  | false =>
    cases h215 : p 215 with
    | false =>
      cases h214 : p 214 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .southWest = some (.walk 214) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_south, advanceAt189_west, advanceAt189_southWest, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, cornerAt189_southWest, h189, h214, h215, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case264.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case264, memberCase264, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame264.bindings p
        intro binding member
        simp only [frame264, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h189
        · exact h214
        · exact h215
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_south, advanceAt189_west, advanceAt189_southWest, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, cornerAt189_southWest, h189, h214, h215, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_south, advanceAt189_west, advanceAt189_southWest, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, cornerAt189_southWest, h189, h215, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 189 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt189_south, advanceAt189_west, advanceAt189_southWest, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, cornerAt189_southWest, h189, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover304 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .north = some outcome) : OracleCovered rowCases304 p outcome := by
  cases h190 : p 190 with
  | false =>
    cases h164 : p 164 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .north = some (.walk 164) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt164_north, advanceAt164_south, advanceAt190_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_north, h164, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case265.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case265, memberCase265, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame265.bindings p
      intro binding member
      simp only [frame265, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h164
      · exact h190
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt164_north, advanceAt164_south, advanceAt190_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_north, h164, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt164_north, advanceAt164_south, advanceAt190_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_north, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover305 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .south = some outcome) : OracleCovered rowCases305 p outcome := by
  cases h190 : p 190 with
  | false =>
    cases h216 : p 216 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .south = some (.walk 216) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt216_north, advanceAt216_south, advanceAt242_south, advanceAt268_south, advanceAt294_south, advanceAt320_south, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt190_south, h190, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case266.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case266, memberCase266, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame266.bindings p
      intro binding member
      simp only [frame266, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h190
      · exact h216
    | true =>
      cases h242 : p 242 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .south = some (.push 216 (.stay 242)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt216_north, advanceAt216_south, advanceAt242_south, advanceAt268_south, advanceAt294_south, advanceAt320_south, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt190_south, h190, h216, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case773.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case773, memberCase773, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame773.bindings p
        intro binding member
        simp only [frame773, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h190
        · exact h216
        · exact h242
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt216_north, advanceAt216_south, advanceAt242_south, advanceAt268_south, advanceAt294_south, advanceAt320_south, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt190_south, h190, h216, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt216_north, advanceAt216_south, advanceAt242_south, advanceAt268_south, advanceAt294_south, advanceAt320_south, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt190_south, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover306 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .east = some outcome) : OracleCovered rowCases306 p outcome := by
  cases h190 : p 190 with
  | false =>
    cases h191 : p 191 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .east = some (.walk 191) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_east, advanceAt191_east, advanceAt191_west, advanceAt192_east, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt190_east, h190, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case267.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case267, memberCase267, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame267.bindings p
      intro binding member
      simp only [frame267, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h190
      · exact h191
    | true =>
      cases h192 : p 192 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .east = some (.push 191 (.stay 192)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_east, advanceAt191_east, advanceAt191_west, advanceAt192_east, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt190_east, h190, h191, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case740.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case740, memberCase740, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame740.bindings p
        intro binding member
        simp only [frame740, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h190
        · exact h191
        · exact h192
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_east, advanceAt191_east, advanceAt191_west, advanceAt192_east, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt190_east, h190, h191, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_east, advanceAt191_east, advanceAt191_west, advanceAt192_east, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt190_east, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover307 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .west = some outcome) : OracleCovered rowCases307 p outcome := by
  cases h190 : p 190 with
  | false =>
    cases h189 : p 189 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .west = some (.walk 189) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_west, advanceAt186_west, advanceAt187_west, advanceAt188_west, advanceAt189_east, advanceAt189_west, advanceAt190_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_west, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case268.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case268, memberCase268, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame268.bindings p
      intro binding member
      simp only [frame268, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h189
      · exact h190
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_west, advanceAt186_west, advanceAt187_west, advanceAt188_west, advanceAt189_east, advanceAt189_west, advanceAt190_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_west, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_west, advanceAt186_west, advanceAt187_west, advanceAt188_west, advanceAt189_east, advanceAt189_west, advanceAt190_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_west, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover308 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .northEast = some outcome) : OracleCovered rowCases308 p outcome := by
  cases h190 : p 190 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_east, advanceAt190_northEast, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt190_northEast, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_east, advanceAt190_northEast, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt190_northEast, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover309 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .northWest = some outcome) : OracleCovered rowCases309 p outcome := by
  cases h190 : p 190 with
  | false =>
    cases h164 : p 164 with
    | false =>
      cases h163 : p 163 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .northWest = some (.walk 163) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_west, advanceAt190_northWest, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_northWest, h163, h164, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case269.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case269, memberCase269, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame269.bindings p
        intro binding member
        simp only [frame269, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h163
        · exact h164
        · exact h190
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_west, advanceAt190_northWest, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_northWest, h163, h164, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h189 : p 189 with
      | false =>
        cases h163 : p 163 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .northWest = some (.walk 163) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_west, advanceAt190_northWest, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_northWest, h163, h164, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case270.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case270, memberCase270, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame270.bindings p
          intro binding member
          simp only [frame270, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h163
          · exact h189
          · exact h190
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_west, advanceAt190_northWest, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_northWest, h163, h164, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_west, advanceAt190_northWest, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_northWest, h164, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_west, advanceAt190_northWest, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_northWest, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover310 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .southEast = some outcome) : OracleCovered rowCases310 p outcome := by
  cases h190 : p 190 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_east, advanceAt190_southEast, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, cornerAt190_southEast, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_east, advanceAt190_southEast, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, cornerAt190_southEast, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover311 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .southWest = some outcome) : OracleCovered rowCases311 p outcome := by
  cases h190 : p 190 with
  | false =>
    cases h216 : p 216 with
    | false =>
      cases h215 : p 215 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .southWest = some (.walk 215) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_west, advanceAt190_southWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt190_southWest, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case271.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case271, memberCase271, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame271.bindings p
        intro binding member
        simp only [frame271, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h190
        · exact h215
        · exact h216
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_west, advanceAt190_southWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt190_southWest, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h189 : p 189 with
      | false =>
        cases h215 : p 215 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .southWest = some (.walk 215) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_west, advanceAt190_southWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt190_southWest, h189, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case272.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case272, memberCase272, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame272.bindings p
          intro binding member
          simp only [frame272, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h189
          · exact h190
          · exact h215
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_west, advanceAt190_southWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt190_southWest, h189, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_west, advanceAt190_southWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt190_southWest, h189, h190, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 190 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_west, advanceAt190_southWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt190_southWest, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P01
