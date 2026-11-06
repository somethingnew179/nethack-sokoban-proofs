import NetHack.Soko12Forward220.Unified.P00.OracleCover24
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover300 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .northEast = some outcome) : OracleCovered rowCases300 p outcome := by
  cases h190 : p 190 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_east, advanceAt190_northEast, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt190_northEast, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_east, advanceAt190_northEast, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt190_northEast, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover301 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .northWest = some outcome) : OracleCovered rowCases301 p outcome := by
  cases h190 : p 190 with
  | false =>
    cases h164 : p 164 with
    | false =>
      cases h163 : p 163 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .northWest = some (.walk 163) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_west, advanceAt190_northWest, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_northWest, h163, h164, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case267.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case267, memberCase267, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame267.bindings p
        intro binding member
        simp only [frame267, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h163
        · exact h164
        · exact h190
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_west, advanceAt190_northWest, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_northWest, h163, h164, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h189 : p 189 with
      | false =>
        cases h163 : p 163 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .northWest = some (.walk 163) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_west, advanceAt190_northWest, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_northWest, h163, h164, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case268.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case268, memberCase268, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame268.bindings p
          intro binding member
          simp only [frame268, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h163
          · exact h189
          · exact h190
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_west, advanceAt190_northWest, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_northWest, h163, h164, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_west, advanceAt190_northWest, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_northWest, h164, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_north, advanceAt190_west, advanceAt190_northWest, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt190_northWest, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover302 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .southEast = some outcome) : OracleCovered rowCases302 p outcome := by
  cases h190 : p 190 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_east, advanceAt190_southEast, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, cornerAt190_southEast, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_east, advanceAt190_southEast, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, cornerAt190_southEast, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover303 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .southWest = some outcome) : OracleCovered rowCases303 p outcome := by
  cases h190 : p 190 with
  | false =>
    cases h216 : p 216 with
    | false =>
      cases h215 : p 215 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .southWest = some (.walk 215) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_west, advanceAt190_southWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt190_southWest, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case269.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case269, memberCase269, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame269.bindings p
        intro binding member
        simp only [frame269, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h190
        · exact h215
        · exact h216
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_west, advanceAt190_southWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt190_southWest, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h189 : p 189 with
      | false =>
        cases h215 : p 215 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .southWest = some (.walk 215) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_west, advanceAt190_southWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt190_southWest, h189, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case270.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case270, memberCase270, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame270.bindings p
          intro binding member
          simp only [frame270, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h189
          · exact h190
          · exact h215
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_west, advanceAt190_southWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt190_southWest, h189, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_west, advanceAt190_southWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt190_southWest, h189, h190, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 190 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt190_south, advanceAt190_west, advanceAt190_southWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt190_southWest, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover304 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .north = some outcome) : OracleCovered rowCases304 p outcome := by
  cases h191 : p 191 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt9_north, advanceAt35_north, advanceAt61_north, advanceAt87_north, advanceAt113_north, advanceAt139_north, advanceAt165_north, advanceAt165_south, advanceAt191_north, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt191_north, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt9_north, advanceAt35_north, advanceAt61_north, advanceAt87_north, advanceAt113_north, advanceAt139_north, advanceAt165_north, advanceAt165_south, advanceAt191_north, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt191_north, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover305 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .south = some outcome) : OracleCovered rowCases305 p outcome := by
  cases h191 : p 191 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_south, advanceAt217_north, advanceAt217_south, advanceAt243_south, advanceAt269_south, advanceAt295_south, advanceAt321_south, advanceAt347_south, advanceAt373_south, advanceAt399_south, advanceAt425_south, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt425, doorAt425, trapAt425, boxAt425, holeAt425, cornerAt191_south, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_south, advanceAt217_north, advanceAt217_south, advanceAt243_south, advanceAt269_south, advanceAt295_south, advanceAt321_south, advanceAt347_south, advanceAt373_south, advanceAt399_south, advanceAt425_south, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt425, doorAt425, trapAt425, boxAt425, holeAt425, cornerAt191_south, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover306 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .east = some outcome) : OracleCovered rowCases306 p outcome := by
  cases h191 : p 191 with
  | false =>
    cases h192 : p 192 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .east = some (.walk 192) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_east, advanceAt192_east, advanceAt192_west, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt191_east, h191, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case271.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case271, memberCase271, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame271.bindings p
      intro binding member
      simp only [frame271, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h191
      · exact h192
    | true =>
      cases h193 : p 193 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .east = some (.push 192 (.stay 193)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_east, advanceAt192_east, advanceAt192_west, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt191_east, h191, h192, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case742.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case742, memberCase742, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame742.bindings p
        intro binding member
        simp only [frame742, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h191
        · exact h192
        · exact h193
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_east, advanceAt192_east, advanceAt192_west, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt191_east, h191, h192, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_east, advanceAt192_east, advanceAt192_west, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt191_east, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover307 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .west = some outcome) : OracleCovered rowCases307 p outcome := by
  cases h191 : p 191 with
  | false =>
    cases h190 : p 190 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .west = some (.walk 190) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_west, advanceAt186_west, advanceAt187_west, advanceAt188_west, advanceAt189_west, advanceAt190_east, advanceAt190_west, advanceAt191_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt191_west, h190, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case272.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case272, memberCase272, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame272.bindings p
      intro binding member
      simp only [frame272, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h190
      · exact h191
    | true =>
      cases h189 : p 189 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .west = some (.push 190 (.stay 189)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_west, advanceAt186_west, advanceAt187_west, advanceAt188_west, advanceAt189_west, advanceAt190_east, advanceAt190_west, advanceAt191_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt191_west, h189, h190, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case737.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case737, memberCase737, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame737.bindings p
        intro binding member
        simp only [frame737, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h189
        · exact h190
        · exact h191
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_west, advanceAt186_west, advanceAt187_west, advanceAt188_west, advanceAt189_west, advanceAt190_east, advanceAt190_west, advanceAt191_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt191_west, h189, h190, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_west, advanceAt186_west, advanceAt187_west, advanceAt188_west, advanceAt189_west, advanceAt190_east, advanceAt190_west, advanceAt191_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt191_west, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover308 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .northEast = some outcome) : OracleCovered rowCases308 p outcome := by
  cases h191 : p 191 with
  | false =>
    cases h192 : p 192 with
    | false =>
      cases h166 : p 166 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .northEast = some (.walk 166) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_north, advanceAt191_east, advanceAt191_northEast, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, cornerAt191_northEast, h166, h191, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case273.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case273, memberCase273, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame273.bindings p
        intro binding member
        simp only [frame273, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h166
        · exact h191
        · exact h192
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_north, advanceAt191_east, advanceAt191_northEast, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, cornerAt191_northEast, h166, h191, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_north, advanceAt191_east, advanceAt191_northEast, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, cornerAt191_northEast, h191, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_north, advanceAt191_east, advanceAt191_northEast, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, cornerAt191_northEast, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover309 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .northWest = some outcome) : OracleCovered rowCases309 p outcome := by
  cases h191 : p 191 with
  | false =>
    cases h190 : p 190 with
    | false =>
      cases h164 : p 164 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .northWest = some (.walk 164) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_north, advanceAt191_west, advanceAt191_northWest, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt191_northWest, h164, h190, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case274.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case274, memberCase274, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame274.bindings p
        intro binding member
        simp only [frame274, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h164
        · exact h190
        · exact h191
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_north, advanceAt191_west, advanceAt191_northWest, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt191_northWest, h164, h190, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_north, advanceAt191_west, advanceAt191_northWest, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt191_northWest, h190, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_north, advanceAt191_west, advanceAt191_northWest, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, cornerAt191_northWest, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover310 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .southEast = some outcome) : OracleCovered rowCases310 p outcome := by
  cases h191 : p 191 with
  | false =>
    cases h192 : p 192 with
    | false =>
      cases h218 : p 218 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .southEast = some (.walk 218) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_south, advanceAt191_east, advanceAt191_southEast, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt191_southEast, h191, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case275.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case275, memberCase275, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame275.bindings p
        intro binding member
        simp only [frame275, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h191
        · exact h192
        · exact h218
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_south, advanceAt191_east, advanceAt191_southEast, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt191_southEast, h191, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_south, advanceAt191_east, advanceAt191_southEast, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt191_southEast, h191, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_south, advanceAt191_east, advanceAt191_southEast, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt191_southEast, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover311 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .southWest = some outcome) : OracleCovered rowCases311 p outcome := by
  cases h191 : p 191 with
  | false =>
    cases h190 : p 190 with
    | false =>
      cases h216 : p 216 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .southWest = some (.walk 216) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_south, advanceAt191_west, advanceAt191_southWest, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, cornerAt191_southWest, h190, h191, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case276.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case276, memberCase276, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame276.bindings p
        intro binding member
        simp only [frame276, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h190
        · exact h191
        · exact h216
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_south, advanceAt191_west, advanceAt191_southWest, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, cornerAt191_southWest, h190, h191, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_south, advanceAt191_west, advanceAt191_southWest, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, cornerAt191_southWest, h190, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 191 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt191_south, advanceAt191_west, advanceAt191_southWest, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, cornerAt191_southWest, h191, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P00
