import NetHack.Soko12Forward220.Unified.P02.OracleCover10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover132 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .northEast = some outcome) : OracleCovered rowCases132 p outcome := by
  cases h133 : p 133 with
  | false =>
    cases h134 : p 134 with
    | false =>
      cases h108 : p 108 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .northEast = some (.walk 108) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_north, advanceAt133_east, advanceAt133_northEast, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt133_northEast, h108, h133, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case076.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case076, memberCase076, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame076.bindings p
        intro binding member
        simp only [frame076, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h108
        · exact h133
        · exact h134
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_north, advanceAt133_east, advanceAt133_northEast, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt133_northEast, h108, h133, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_north, advanceAt133_east, advanceAt133_northEast, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt133_northEast, h133, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_north, advanceAt133_east, advanceAt133_northEast, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt133_northEast, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover133 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .northWest = some outcome) : OracleCovered rowCases133 p outcome := by
  cases h133 : p 133 with
  | false =>
    cases h132 : p 132 with
    | false =>
      cases h106 : p 106 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .northWest = some (.walk 106) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_north, advanceAt133_west, advanceAt133_northWest, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, cornerAt133_northWest, h106, h132, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case077.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case077, memberCase077, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame077.bindings p
        intro binding member
        simp only [frame077, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h106
        · exact h132
        · exact h133
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_north, advanceAt133_west, advanceAt133_northWest, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, cornerAt133_northWest, h106, h132, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_north, advanceAt133_west, advanceAt133_northWest, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, cornerAt133_northWest, h132, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_north, advanceAt133_west, advanceAt133_northWest, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, cornerAt133_northWest, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover134 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southEast = some outcome) : OracleCovered rowCases134 p outcome := by
  cases h133 : p 133 with
  | false =>
    cases h159 : p 159 with
    | false =>
      cases h160 : p 160 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southEast = some (.walk 160) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_south, advanceAt133_east, advanceAt133_southEast, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt133_southEast, h133, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case078.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case078, memberCase078, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame078.bindings p
        intro binding member
        simp only [frame078, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h133
        · exact h159
        · exact h160
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_south, advanceAt133_east, advanceAt133_southEast, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt133_southEast, h133, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h134 : p 134 with
      | false =>
        cases h160 : p 160 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southEast = some (.walk 160) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_south, advanceAt133_east, advanceAt133_southEast, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt133_southEast, h133, h134, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case079.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case079, memberCase079, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame079.bindings p
          intro binding member
          simp only [frame079, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h133
          · exact h134
          · exact h160
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_south, advanceAt133_east, advanceAt133_southEast, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt133_southEast, h133, h134, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_south, advanceAt133_east, advanceAt133_southEast, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt133_southEast, h133, h134, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_south, advanceAt133_east, advanceAt133_southEast, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt133_southEast, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover135 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southWest = some outcome) : OracleCovered rowCases135 p outcome := by
  cases h133 : p 133 with
  | false =>
    cases h159 : p 159 with
    | false =>
      cases h158 : p 158 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southWest = some (.walk 158) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_south, advanceAt133_west, advanceAt133_southWest, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt133_southWest, h133, h158, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case080.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case080, memberCase080, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame080.bindings p
        intro binding member
        simp only [frame080, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h133
        · exact h158
        · exact h159
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_south, advanceAt133_west, advanceAt133_southWest, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt133_southWest, h133, h158, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h132 : p 132 with
      | false =>
        cases h158 : p 158 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southWest = some (.walk 158) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_south, advanceAt133_west, advanceAt133_southWest, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt133_southWest, h132, h133, h158, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case081.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case081, memberCase081, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame081.bindings p
          intro binding member
          simp only [frame081, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h132
          · exact h133
          · exact h158
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_south, advanceAt133_west, advanceAt133_southWest, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt133_southWest, h132, h133, h158, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_south, advanceAt133_west, advanceAt133_southWest, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt133_southWest, h132, h133, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 133 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt133_south, advanceAt133_west, advanceAt133_southWest, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt133_southWest, h133, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover136 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .north = some outcome) : OracleCovered rowCases136 p outcome := by
  cases h134 : p 134 with
  | false =>
    cases h108 : p 108 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .north = some (.walk 108) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt108_south, advanceAt134_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt134_north, h108, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case082.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case082, memberCase082, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame082.bindings p
      intro binding member
      simp only [frame082, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h108
      · exact h134
    | true =>
      cases h82 : p 82 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .north = some (.push 108 (.stay 82)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt108_south, advanceAt134_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt134_north, h82, h108, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case674.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case674, memberCase674, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame674.bindings p
        intro binding member
        simp only [frame674, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h82
        · exact h108
        · exact h134
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt108_south, advanceAt134_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt134_north, h82, h108, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt108_south, advanceAt134_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt134_north, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover137 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .south = some outcome) : OracleCovered rowCases137 p outcome := by
  cases h134 : p 134 with
  | false =>
    cases h160 : p 160 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .south = some (.walk 160) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt160_north, advanceAt160_south, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt134_south, h134, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case083.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case083, memberCase083, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame083.bindings p
      intro binding member
      simp only [frame083, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h134
      · exact h160
    | true =>
      cases h186 : p 186 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .south = some (.push 160 (.stay 186)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt160_north, advanceAt160_south, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt134_south, h134, h160, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case709.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case709, memberCase709, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame709.bindings p
        intro binding member
        simp only [frame709, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h134
        · exact h160
        · exact h186
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt160_north, advanceAt160_south, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt134_south, h134, h160, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt160_north, advanceAt160_south, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt134_south, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover138 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .east = some outcome) : OracleCovered rowCases138 p outcome := by
  cases h134 : p 134 with
  | false =>
    cases h135 : p 135 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .east = some (.walk 135) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_east, advanceAt135_east, advanceAt135_west, advanceAt136_east, advanceAt137_east, advanceAt138_east, advanceAt139_east, advanceAt140_east, advanceAt141_east, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt134_east, h134, h135, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case084.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case084, memberCase084, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame084.bindings p
      intro binding member
      simp only [frame084, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h134
      · exact h135
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_east, advanceAt135_east, advanceAt135_west, advanceAt136_east, advanceAt137_east, advanceAt138_east, advanceAt139_east, advanceAt140_east, advanceAt141_east, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt134_east, h134, h135, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_east, advanceAt135_east, advanceAt135_west, advanceAt136_east, advanceAt137_east, advanceAt138_east, advanceAt139_east, advanceAt140_east, advanceAt141_east, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt134_east, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover139 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .west = some outcome) : OracleCovered rowCases139 p outcome := by
  cases h134 : p 134 with
  | false =>
    cases h133 : p 133 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .west = some (.walk 133) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_east, advanceAt133_west, advanceAt134_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt134_west, h133, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case085.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case085, memberCase085, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame085.bindings p
      intro binding member
      simp only [frame085, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h133
      · exact h134
    | true =>
      cases h132 : p 132 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .west = some (.push 133 (.stay 132)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_east, advanceAt133_west, advanceAt134_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt134_west, h132, h133, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case685.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case685, memberCase685, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame685.bindings p
        intro binding member
        simp only [frame685, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h132
        · exact h133
        · exact h134
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_east, advanceAt133_west, advanceAt134_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt134_west, h132, h133, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_east, advanceAt133_west, advanceAt134_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt134_west, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover140 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .northEast = some outcome) : OracleCovered rowCases140 p outcome := by
  cases h134 : p 134 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_north, advanceAt134_east, advanceAt134_northEast, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, cornerAt134_northEast, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_north, advanceAt134_east, advanceAt134_northEast, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, cornerAt134_northEast, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover141 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .northWest = some outcome) : OracleCovered rowCases141 p outcome := by
  cases h134 : p 134 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_north, advanceAt134_west, advanceAt134_northWest, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt134_northWest, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_north, advanceAt134_west, advanceAt134_northWest, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, cornerAt134_northWest, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover142 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southEast = some outcome) : OracleCovered rowCases142 p outcome := by
  cases h134 : p 134 with
  | false =>
    cases h160 : p 160 with
    | false =>
      cases h161 : p 161 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southEast = some (.walk 161) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt134_east, advanceAt134_southEast, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt134_southEast, h134, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case086.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case086, memberCase086, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame086.bindings p
        intro binding member
        simp only [frame086, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h134
        · exact h160
        · exact h161
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt134_east, advanceAt134_southEast, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt134_southEast, h134, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h135 : p 135 with
      | false =>
        cases h161 : p 161 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southEast = some (.walk 161) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt134_east, advanceAt134_southEast, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt134_southEast, h134, h135, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case087.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case087, memberCase087, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame087.bindings p
          intro binding member
          simp only [frame087, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h134
          · exact h135
          · exact h161
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt134_east, advanceAt134_southEast, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt134_southEast, h134, h135, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt134_east, advanceAt134_southEast, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt134_southEast, h134, h135, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt134_east, advanceAt134_southEast, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt134_southEast, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover143 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southWest = some outcome) : OracleCovered rowCases143 p outcome := by
  cases h134 : p 134 with
  | false =>
    cases h160 : p 160 with
    | false =>
      cases h159 : p 159 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southWest = some (.walk 159) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt134_west, advanceAt134_southWest, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt134_southWest, h134, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case088.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case088, memberCase088, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame088.bindings p
        intro binding member
        simp only [frame088, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h134
        · exact h159
        · exact h160
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt134_west, advanceAt134_southWest, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt134_southWest, h134, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h133 : p 133 with
      | false =>
        cases h159 : p 159 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southWest = some (.walk 159) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt134_west, advanceAt134_southWest, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt134_southWest, h133, h134, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case089.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case089, memberCase089, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame089.bindings p
          intro binding member
          simp only [frame089, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h133
          · exact h134
          · exact h159
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt134_west, advanceAt134_southWest, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt134_southWest, h133, h134, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt134_west, advanceAt134_southWest, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt134_southWest, h133, h134, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 134 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt134_south, advanceAt134_west, advanceAt134_southWest, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt134_southWest, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P02
