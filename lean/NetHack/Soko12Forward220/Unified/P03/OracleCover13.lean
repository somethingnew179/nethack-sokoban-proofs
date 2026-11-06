import NetHack.Soko12Forward220.Unified.P03.OracleCover12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover156 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .northEast = some outcome) : OracleCovered rowCases156 p outcome := by
  cases h135 : p 135 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_north, advanceAt135_east, advanceAt135_northEast, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, cornerAt135_northEast, h135, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_north, advanceAt135_east, advanceAt135_northEast, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, cornerAt135_northEast, h135, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover157 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .northWest = some outcome) : OracleCovered rowCases157 p outcome := by
  cases h135 : p 135 with
  | false =>
    cases h134 : p 134 with
    | false =>
      cases h108 : p 108 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .northWest = some (.walk 108) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_north, advanceAt135_west, advanceAt135_northWest, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, cornerAt135_northWest, h108, h134, h135, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case094.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case094, memberCase094, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame094.bindings p
        intro binding member
        simp only [frame094, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h108
        · exact h134
        · exact h135
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_north, advanceAt135_west, advanceAt135_northWest, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, cornerAt135_northWest, h108, h134, h135, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_north, advanceAt135_west, advanceAt135_northWest, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, cornerAt135_northWest, h134, h135, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_north, advanceAt135_west, advanceAt135_northWest, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, cornerAt135_northWest, h135, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover158 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .southEast = some outcome) : OracleCovered rowCases158 p outcome := by
  cases h135 : p 135 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_south, advanceAt135_east, advanceAt135_southEast, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, cornerAt135_southEast, h135, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_south, advanceAt135_east, advanceAt135_southEast, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, cornerAt135_southEast, h135, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover159 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .southWest = some outcome) : OracleCovered rowCases159 p outcome := by
  cases h135 : p 135 with
  | false =>
    cases h161 : p 161 with
    | false =>
      cases h160 : p 160 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .southWest = some (.walk 160) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_south, advanceAt135_west, advanceAt135_southWest, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt135_southWest, h135, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case095.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case095, memberCase095, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame095.bindings p
        intro binding member
        simp only [frame095, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h135
        · exact h160
        · exact h161
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_south, advanceAt135_west, advanceAt135_southWest, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt135_southWest, h135, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h134 : p 134 with
      | false =>
        cases h160 : p 160 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .southWest = some (.walk 160) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_south, advanceAt135_west, advanceAt135_southWest, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt135_southWest, h134, h135, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case096.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case096, memberCase096, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame096.bindings p
          intro binding member
          simp only [frame096, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h134
          · exact h135
          · exact h160
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_south, advanceAt135_west, advanceAt135_southWest, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt135_southWest, h134, h135, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_south, advanceAt135_west, advanceAt135_southWest, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt135_southWest, h134, h135, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 135 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt135_south, advanceAt135_west, advanceAt135_southWest, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt135_southWest, h135, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover160 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .north = some outcome) : OracleCovered rowCases160 p outcome := by
  cases h140 : p 140 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt114_south, advanceAt140_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt140_north, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt114_south, advanceAt140_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt140_north, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover161 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .south = some outcome) : OracleCovered rowCases161 p outcome := by
  cases h140 : p 140 with
  | false =>
    cases h166 : p 166 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .south = some (.walk 166) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt166_north, advanceAt166_south, advanceAt192_south, advanceAt218_south, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt140_south, h140, h166, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case097.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case097, memberCase097, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame097.bindings p
      intro binding member
      simp only [frame097, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h140
      · exact h166
    | true =>
      cases h192 : p 192 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .south = some (.push 166 (.stay 192)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt166_north, advanceAt166_south, advanceAt192_south, advanceAt218_south, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt140_south, h140, h166, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case717.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case717, memberCase717, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame717.bindings p
        intro binding member
        simp only [frame717, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h140
        · exact h166
        · exact h192
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt166_north, advanceAt166_south, advanceAt192_south, advanceAt218_south, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt140_south, h140, h166, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt166_north, advanceAt166_south, advanceAt192_south, advanceAt218_south, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt140_south, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover162 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .east = some outcome) : OracleCovered rowCases162 p outcome := by
  cases h140 : p 140 with
  | false =>
    cases h141 : p 141 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .east = some (.walk 141) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_east, advanceAt141_east, advanceAt141_west, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt140_east, h140, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case098.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case098, memberCase098, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame098.bindings p
      intro binding member
      simp only [frame098, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h140
      · exact h141
    | true =>
      cases h142 : p 142 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .east = some (.push 141 (.stay 142)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_east, advanceAt141_east, advanceAt141_west, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt140_east, h140, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case694.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case694, memberCase694, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame694.bindings p
        intro binding member
        simp only [frame694, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h140
        · exact h141
        · exact h142
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_east, advanceAt141_east, advanceAt141_west, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt140_east, h140, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_east, advanceAt141_east, advanceAt141_west, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt140_east, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover163 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .west = some outcome) : OracleCovered rowCases163 p outcome := by
  cases h140 : p 140 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_east, advanceAt139_west, advanceAt140_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt140_west, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_east, advanceAt139_west, advanceAt140_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt140_west, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover164 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .northEast = some outcome) : OracleCovered rowCases164 p outcome := by
  cases h140 : p 140 with
  | false =>
    cases h141 : p 141 with
    | false =>
      cases h115 : p 115 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .northEast = some (.walk 115) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_north, advanceAt140_east, advanceAt140_northEast, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt140_northEast, h115, h140, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case099.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case099, memberCase099, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame099.bindings p
        intro binding member
        simp only [frame099, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h115
        · exact h140
        · exact h141
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_north, advanceAt140_east, advanceAt140_northEast, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt140_northEast, h115, h140, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_north, advanceAt140_east, advanceAt140_northEast, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt140_northEast, h140, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_north, advanceAt140_east, advanceAt140_northEast, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt140_northEast, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover165 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .northWest = some outcome) : OracleCovered rowCases165 p outcome := by
  cases h140 : p 140 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_north, advanceAt140_west, advanceAt140_northWest, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt140_northWest, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_north, advanceAt140_west, advanceAt140_northWest, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt140_northWest, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover166 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .southEast = some outcome) : OracleCovered rowCases166 p outcome := by
  cases h140 : p 140 with
  | false =>
    cases h166 : p 166 with
    | false =>
      cases h167 : p 167 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .southEast = some (.walk 167) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_east, advanceAt140_southEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt140_southEast, h140, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case100.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case100, memberCase100, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame100.bindings p
        intro binding member
        simp only [frame100, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h140
        · exact h166
        · exact h167
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_east, advanceAt140_southEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt140_southEast, h140, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h141 : p 141 with
      | false =>
        cases h167 : p 167 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .southEast = some (.walk 167) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_east, advanceAt140_southEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt140_southEast, h140, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case101.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case101, memberCase101, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame101.bindings p
          intro binding member
          simp only [frame101, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h140
          · exact h141
          · exact h167
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_east, advanceAt140_southEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt140_southEast, h140, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_east, advanceAt140_southEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt140_southEast, h140, h141, h166, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_east, advanceAt140_southEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt140_southEast, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover167 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .southWest = some outcome) : OracleCovered rowCases167 p outcome := by
  cases h140 : p 140 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_west, advanceAt140_southWest, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, cornerAt140_southWest, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 140 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_west, advanceAt140_southWest, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, cornerAt140_southWest, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P03
