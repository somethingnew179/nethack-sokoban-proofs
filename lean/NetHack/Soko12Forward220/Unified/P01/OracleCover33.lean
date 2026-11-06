import NetHack.Soko12Forward220.Unified.P01.OracleCover32
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover396 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .northEast = some outcome) : OracleCovered rowCases396 p outcome := by
  cases h216 : p 216 with
  | false =>
    cases h190 : p 190 with
    | false =>
      cases h191 : p 191 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .northEast = some (.walk 191) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_north, advanceAt216_east, advanceAt216_northEast, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, cornerAt216_northEast, h190, h191, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case363.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case363, memberCase363, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame363.bindings p
        intro binding member
        simp only [frame363, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h190
        · exact h191
        · exact h216
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_north, advanceAt216_east, advanceAt216_northEast, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, cornerAt216_northEast, h190, h191, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_north, advanceAt216_east, advanceAt216_northEast, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, cornerAt216_northEast, h190, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_north, advanceAt216_east, advanceAt216_northEast, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, cornerAt216_northEast, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover397 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .northWest = some outcome) : OracleCovered rowCases397 p outcome := by
  cases h216 : p 216 with
  | false =>
    cases h190 : p 190 with
    | false =>
      cases h189 : p 189 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .northWest = some (.walk 189) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_north, advanceAt216_west, advanceAt216_northWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt216_northWest, h189, h190, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case364.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case364, memberCase364, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame364.bindings p
        intro binding member
        simp only [frame364, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h189
        · exact h190
        · exact h216
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_north, advanceAt216_west, advanceAt216_northWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt216_northWest, h189, h190, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h215 : p 215 with
      | false =>
        cases h189 : p 189 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .northWest = some (.walk 189) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_north, advanceAt216_west, advanceAt216_northWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt216_northWest, h189, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case365.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case365, memberCase365, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame365.bindings p
          intro binding member
          simp only [frame365, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h189
          · exact h215
          · exact h216
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_north, advanceAt216_west, advanceAt216_northWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt216_northWest, h189, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_north, advanceAt216_west, advanceAt216_northWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt216_northWest, h190, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_north, advanceAt216_west, advanceAt216_northWest, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, cornerAt216_northWest, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover398 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .southEast = some outcome) : OracleCovered rowCases398 p outcome := by
  cases h216 : p 216 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_south, advanceAt216_east, advanceAt216_southEast, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, cornerAt216_southEast, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_south, advanceAt216_east, advanceAt216_southEast, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, cornerAt216_southEast, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover399 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .southWest = some outcome) : OracleCovered rowCases399 p outcome := by
  cases h216 : p 216 with
  | false =>
    cases h242 : p 242 with
    | false =>
      cases h241 : p 241 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .southWest = some (.walk 241) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_south, advanceAt216_west, advanceAt216_southWest, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt216_southWest, h216, h241, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case366.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case366, memberCase366, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame366.bindings p
        intro binding member
        simp only [frame366, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h216
        · exact h241
        · exact h242
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_south, advanceAt216_west, advanceAt216_southWest, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt216_southWest, h216, h241, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h215 : p 215 with
      | false =>
        cases h241 : p 241 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .southWest = some (.walk 241) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_south, advanceAt216_west, advanceAt216_southWest, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt216_southWest, h215, h216, h241, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case367.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case367, memberCase367, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame367.bindings p
          intro binding member
          simp only [frame367, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h215
          · exact h216
          · exact h241
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_south, advanceAt216_west, advanceAt216_southWest, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt216_southWest, h215, h216, h241, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_south, advanceAt216_west, advanceAt216_southWest, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt216_southWest, h215, h216, h242, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 216 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt216_south, advanceAt216_west, advanceAt216_southWest, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, cornerAt216_southWest, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover400 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .north = some outcome) : OracleCovered rowCases400 p outcome := by
  cases h218 : p 218 with
  | false =>
    cases h192 : p 192 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .north = some (.walk 192) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt192_south, advanceAt218_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_north, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case368.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case368, memberCase368, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame368.bindings p
      intro binding member
      simp only [frame368, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h192
      · exact h218
    | true =>
      cases h166 : p 166 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .north = some (.push 192 (.stay 166)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt192_south, advanceAt218_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_north, h166, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case742.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case742, memberCase742, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame742.bindings p
        intro binding member
        simp only [frame742, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h166
        · exact h192
        · exact h218
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt192_south, advanceAt218_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_north, h166, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt192_south, advanceAt218_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_north, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover401 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .south = some outcome) : OracleCovered rowCases401 p outcome := by
  cases h218 : p 218 with
  | false =>
    cases h244 : p 244 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .south = some (.walk 244) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt244_north, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt218_south, h218, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case369.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case369, memberCase369, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame369.bindings p
      intro binding member
      simp only [frame369, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h218
      · exact h244
    | true =>
      cases h270 : p 270 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .south = some (.push 244 (.stay 270)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt244_north, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt218_south, h218, h244, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case795.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case795, memberCase795, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame795.bindings p
        intro binding member
        simp only [frame795, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h218
        · exact h244
        · exact h270
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt244_north, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt218_south, h218, h244, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt244_north, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt218_south, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover402 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .east = some outcome) : OracleCovered rowCases402 p outcome := by
  cases h218 : p 218 with
  | false =>
    cases h219 : p 219 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .east = some (.walk 219) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_east, advanceAt219_east, advanceAt219_west, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt218_east, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case370.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case370, memberCase370, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame370.bindings p
      intro binding member
      simp only [frame370, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h218
      · exact h219
    | true =>
      cases h220 : p 220 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .east = some (.push 219 (.stay 220)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_east, advanceAt219_east, advanceAt219_west, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt218_east, h218, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case778.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case778, memberCase778, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame778.bindings p
        intro binding member
        simp only [frame778, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h218
        · exact h219
        · exact h220
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_east, advanceAt219_east, advanceAt219_west, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt218_east, h218, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_east, advanceAt219_east, advanceAt219_west, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt218_east, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover403 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .west = some outcome) : OracleCovered rowCases403 p outcome := by
  cases h218 : p 218 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_west, advanceAt214_west, advanceAt215_west, advanceAt216_west, advanceAt217_east, advanceAt217_west, advanceAt218_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_west, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_west, advanceAt214_west, advanceAt215_west, advanceAt216_west, advanceAt217_east, advanceAt217_west, advanceAt218_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_west, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover404 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .northEast = some outcome) : OracleCovered rowCases404 p outcome := by
  cases h218 : p 218 with
  | false =>
    cases h192 : p 192 with
    | false =>
      cases h193 : p 193 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .northEast = some (.walk 193) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, h192, h193, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case371.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case371, memberCase371, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame371.bindings p
        intro binding member
        simp only [frame371, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h192
        · exact h193
        · exact h218
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, h192, h193, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h219 : p 219 with
      | false =>
        cases h193 : p 193 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .northEast = some (.walk 193) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, h192, h193, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case372.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case372, memberCase372, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame372.bindings p
          intro binding member
          simp only [frame372, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h193
          · exact h218
          · exact h219
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, h192, h193, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, h192, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover405 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .northWest = some outcome) : OracleCovered rowCases405 p outcome := by
  cases h218 : p 218 with
  | false =>
    cases h192 : p 192 with
    | false =>
      cases h191 : p 191 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .northWest = some (.walk 191) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_west, advanceAt218_northWest, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_northWest, h191, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case373.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case373, memberCase373, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame373.bindings p
        intro binding member
        simp only [frame373, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h191
        · exact h192
        · exact h218
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_west, advanceAt218_northWest, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_northWest, h191, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_west, advanceAt218_northWest, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_northWest, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_west, advanceAt218_northWest, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_northWest, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover406 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .southEast = some outcome) : OracleCovered rowCases406 p outcome := by
  cases h218 : p 218 with
  | false =>
    cases h244 : p 244 with
    | false =>
      cases h245 : p 245 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .southEast = some (.walk 245) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt218_southEast, h218, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case374.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case374, memberCase374, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame374.bindings p
        intro binding member
        simp only [frame374, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h218
        · exact h244
        · exact h245
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt218_southEast, h218, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h219 : p 219 with
      | false =>
        cases h245 : p 245 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .southEast = some (.walk 245) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt218_southEast, h218, h219, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case375.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case375, memberCase375, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame375.bindings p
          intro binding member
          simp only [frame375, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h218
          · exact h219
          · exact h245
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt218_southEast, h218, h219, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt218_southEast, h218, h219, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt218_southEast, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover407 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .southWest = some outcome) : OracleCovered rowCases407 p outcome := by
  cases h218 : p 218 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_west, advanceAt218_southWest, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, cornerAt218_southWest, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 218 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_west, advanceAt218_southWest, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, cornerAt218_southWest, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P01
