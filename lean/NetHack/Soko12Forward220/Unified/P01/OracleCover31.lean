import NetHack.Soko12Forward220.Unified.P01.OracleCover30
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover372 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .northEast = some outcome) : OracleCovered rowCases372 p outcome := by
  cases h213 : p 213 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_north, advanceAt213_east, advanceAt213_northEast, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, cornerAt213_northEast, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_north, advanceAt213_east, advanceAt213_northEast, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, cornerAt213_northEast, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover373 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .northWest = some outcome) : OracleCovered rowCases373 p outcome := by
  cases h213 : p 213 with
  | false =>
    cases h187 : p 187 with
    | false =>
      cases h186 : p 186 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .northWest = some (.walk 186) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_north, advanceAt213_west, advanceAt213_northWest, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, cornerAt213_northWest, h186, h187, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case342.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case342, memberCase342, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame342.bindings p
        intro binding member
        simp only [frame342, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h186
        · exact h187
        · exact h213
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_north, advanceAt213_west, advanceAt213_northWest, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, cornerAt213_northWest, h186, h187, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h212 : p 212 with
      | false =>
        cases h186 : p 186 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .northWest = some (.walk 186) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_north, advanceAt213_west, advanceAt213_northWest, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, cornerAt213_northWest, h186, h187, h212, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case343.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case343, memberCase343, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame343.bindings p
          intro binding member
          simp only [frame343, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h186
          · exact h212
          · exact h213
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_north, advanceAt213_west, advanceAt213_northWest, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, cornerAt213_northWest, h186, h187, h212, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_north, advanceAt213_west, advanceAt213_northWest, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, cornerAt213_northWest, h187, h212, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_north, advanceAt213_west, advanceAt213_northWest, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, cornerAt213_northWest, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover374 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .southEast = some outcome) : OracleCovered rowCases374 p outcome := by
  cases h213 : p 213 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_south, advanceAt213_east, advanceAt213_southEast, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, cornerAt213_southEast, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_south, advanceAt213_east, advanceAt213_southEast, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, cornerAt213_southEast, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover375 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .southWest = some outcome) : OracleCovered rowCases375 p outcome := by
  cases h213 : p 213 with
  | false =>
    cases h239 : p 239 with
    | false =>
      cases h238 : p 238 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .southWest = some (.walk 238) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_south, advanceAt213_west, advanceAt213_southWest, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, cornerAt213_southWest, h213, h238, h239, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case344.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case344, memberCase344, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame344.bindings p
        intro binding member
        simp only [frame344, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h213
        · exact h238
        · exact h239
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_south, advanceAt213_west, advanceAt213_southWest, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, cornerAt213_southWest, h213, h238, h239, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h212 : p 212 with
      | false =>
        cases h238 : p 238 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .southWest = some (.walk 238) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_south, advanceAt213_west, advanceAt213_southWest, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, cornerAt213_southWest, h212, h213, h238, h239, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case345.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case345, memberCase345, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame345.bindings p
          intro binding member
          simp only [frame345, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h212
          · exact h213
          · exact h238
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_south, advanceAt213_west, advanceAt213_southWest, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, cornerAt213_southWest, h212, h213, h238, h239, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_south, advanceAt213_west, advanceAt213_southWest, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, cornerAt213_southWest, h212, h213, h239, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 213 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt213_south, advanceAt213_west, advanceAt213_southWest, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, cornerAt213_southWest, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover376 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .north = some outcome) : OracleCovered rowCases376 p outcome := by
  cases h214 : p 214 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt188_south, advanceAt214_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, cornerAt214_north, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt188_south, advanceAt214_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, cornerAt214_north, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover377 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .south = some outcome) : OracleCovered rowCases377 p outcome := by
  cases h214 : p 214 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_south, advanceAt240_north, advanceAt240_south, advanceAt266_south, advanceAt292_south, advanceAt318_south, advanceAt344_south, advanceAt370_south, advanceAt396_south, advanceAt422_south, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, cornerAt214_south, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_south, advanceAt240_north, advanceAt240_south, advanceAt266_south, advanceAt292_south, advanceAt318_south, advanceAt344_south, advanceAt370_south, advanceAt396_south, advanceAt422_south, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, cornerAt214_south, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover378 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .east = some outcome) : OracleCovered rowCases378 p outcome := by
  cases h214 : p 214 with
  | false =>
    cases h215 : p 215 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .east = some (.walk 215) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_east, advanceAt215_east, advanceAt215_west, advanceAt216_east, advanceAt217_east, advanceAt218_east, advanceAt219_east, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt214_east, h214, h215, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case346.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case346, memberCase346, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame346.bindings p
      intro binding member
      simp only [frame346, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h214
      · exact h215
    | true =>
      cases h216 : p 216 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .east = some (.push 215 (.stay 216)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_east, advanceAt215_east, advanceAt215_west, advanceAt216_east, advanceAt217_east, advanceAt218_east, advanceAt219_east, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt214_east, h214, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case770.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case770, memberCase770, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame770.bindings p
        intro binding member
        simp only [frame770, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h214
        · exact h215
        · exact h216
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_east, advanceAt215_east, advanceAt215_west, advanceAt216_east, advanceAt217_east, advanceAt218_east, advanceAt219_east, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt214_east, h214, h215, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_east, advanceAt215_east, advanceAt215_west, advanceAt216_east, advanceAt217_east, advanceAt218_east, advanceAt219_east, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt214_east, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover379 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .west = some outcome) : OracleCovered rowCases379 p outcome := by
  cases h214 : p 214 with
  | false =>
    cases h213 : p 213 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .west = some (.walk 213) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_east, advanceAt213_west, advanceAt214_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, cornerAt214_west, h213, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case347.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case347, memberCase347, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame347.bindings p
      intro binding member
      simp only [frame347, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h213
      · exact h214
    | true =>
      cases h212 : p 212 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .west = some (.push 213 (.stay 212)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_east, advanceAt213_west, advanceAt214_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, cornerAt214_west, h212, h213, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case765.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case765, memberCase765, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame765.bindings p
        intro binding member
        simp only [frame765, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h212
        · exact h213
        · exact h214
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_east, advanceAt213_west, advanceAt214_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, cornerAt214_west, h212, h213, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_east, advanceAt213_west, advanceAt214_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, cornerAt214_west, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover380 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .northEast = some outcome) : OracleCovered rowCases380 p outcome := by
  cases h214 : p 214 with
  | false =>
    cases h215 : p 215 with
    | false =>
      cases h189 : p 189 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .northEast = some (.walk 189) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_north, advanceAt214_east, advanceAt214_northEast, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, cornerAt214_northEast, h189, h214, h215, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case348.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case348, memberCase348, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame348.bindings p
        intro binding member
        simp only [frame348, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h189
        · exact h214
        · exact h215
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_north, advanceAt214_east, advanceAt214_northEast, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, cornerAt214_northEast, h189, h214, h215, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_north, advanceAt214_east, advanceAt214_northEast, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, cornerAt214_northEast, h214, h215, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_north, advanceAt214_east, advanceAt214_northEast, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, cornerAt214_northEast, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover381 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .northWest = some outcome) : OracleCovered rowCases381 p outcome := by
  cases h214 : p 214 with
  | false =>
    cases h213 : p 213 with
    | false =>
      cases h187 : p 187 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .northWest = some (.walk 187) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_north, advanceAt214_west, advanceAt214_northWest, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, cornerAt214_northWest, h187, h213, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case349.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case349, memberCase349, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame349.bindings p
        intro binding member
        simp only [frame349, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h187
        · exact h213
        · exact h214
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_north, advanceAt214_west, advanceAt214_northWest, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, cornerAt214_northWest, h187, h213, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_north, advanceAt214_west, advanceAt214_northWest, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, cornerAt214_northWest, h213, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_north, advanceAt214_west, advanceAt214_northWest, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, cornerAt214_northWest, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover382 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .southEast = some outcome) : OracleCovered rowCases382 p outcome := by
  cases h214 : p 214 with
  | false =>
    cases h215 : p 215 with
    | false =>
      cases h241 : p 241 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .southEast = some (.walk 241) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_south, advanceAt214_east, advanceAt214_southEast, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt214_southEast, h214, h215, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case350.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case350, memberCase350, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame350.bindings p
        intro binding member
        simp only [frame350, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h214
        · exact h215
        · exact h241
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_south, advanceAt214_east, advanceAt214_southEast, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt214_southEast, h214, h215, h241, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_south, advanceAt214_east, advanceAt214_southEast, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt214_southEast, h214, h215, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_south, advanceAt214_east, advanceAt214_southEast, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, cornerAt214_southEast, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover383 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .southWest = some outcome) : OracleCovered rowCases383 p outcome := by
  cases h214 : p 214 with
  | false =>
    cases h213 : p 213 with
    | false =>
      cases h239 : p 239 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .southWest = some (.walk 239) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_south, advanceAt214_west, advanceAt214_southWest, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, cornerAt214_southWest, h213, h214, h239, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case351.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case351, memberCase351, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame351.bindings p
        intro binding member
        simp only [frame351, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h213
        · exact h214
        · exact h239
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_south, advanceAt214_west, advanceAt214_southWest, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, cornerAt214_southWest, h213, h214, h239, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_south, advanceAt214_west, advanceAt214_southWest, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, cornerAt214_southWest, h213, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 214 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt214_south, advanceAt214_west, advanceAt214_southWest, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, cornerAt214_southWest, h214, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P01
