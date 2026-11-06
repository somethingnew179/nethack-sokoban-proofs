import NetHack.Soko12Forward220.Unified.P01.OracleCover12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover156 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .northEast = some outcome) : OracleCovered rowCases156 p outcome := by
  cases h141 : p 141 with
  | false =>
    cases h115 : p 115 with
    | false =>
      cases h116 : p 116 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .northEast = some (.walk 116) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_north, advanceAt141_east, advanceAt141_northEast, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt141_northEast, h115, h116, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case102.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case102, memberCase102, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame102.bindings p
        intro binding member
        simp only [frame102, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h115
        · exact h116
        · exact h141
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_north, advanceAt141_east, advanceAt141_northEast, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt141_northEast, h115, h116, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h142 : p 142 with
      | false =>
        cases h116 : p 116 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .northEast = some (.walk 116) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_north, advanceAt141_east, advanceAt141_northEast, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt141_northEast, h115, h116, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case103.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case103, memberCase103, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame103.bindings p
          intro binding member
          simp only [frame103, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h116
          · exact h141
          · exact h142
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_north, advanceAt141_east, advanceAt141_northEast, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt141_northEast, h115, h116, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_north, advanceAt141_east, advanceAt141_northEast, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt141_northEast, h115, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_north, advanceAt141_east, advanceAt141_northEast, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt141_northEast, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover157 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .northWest = some outcome) : OracleCovered rowCases157 p outcome := by
  cases h141 : p 141 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_north, advanceAt141_west, advanceAt141_northWest, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt141_northWest, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_north, advanceAt141_west, advanceAt141_northWest, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt141_northWest, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover158 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southEast = some outcome) : OracleCovered rowCases158 p outcome := by
  cases h141 : p 141 with
  | false =>
    cases h167 : p 167 with
    | false =>
      cases h168 : p 168 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southEast = some (.walk 168) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt141_east, advanceAt141_southEast, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt141_southEast, h141, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case104.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case104, memberCase104, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame104.bindings p
        intro binding member
        simp only [frame104, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h141
        · exact h167
        · exact h168
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt141_east, advanceAt141_southEast, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt141_southEast, h141, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h142 : p 142 with
      | false =>
        cases h168 : p 168 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southEast = some (.walk 168) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt141_east, advanceAt141_southEast, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt141_southEast, h141, h142, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case105.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case105, memberCase105, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame105.bindings p
          intro binding member
          simp only [frame105, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h141
          · exact h142
          · exact h168
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt141_east, advanceAt141_southEast, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt141_southEast, h141, h142, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt141_east, advanceAt141_southEast, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt141_southEast, h141, h142, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt141_east, advanceAt141_southEast, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt141_southEast, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover159 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southWest = some outcome) : OracleCovered rowCases159 p outcome := by
  cases h141 : p 141 with
  | false =>
    cases h167 : p 167 with
    | false =>
      cases h166 : p 166 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southWest = some (.walk 166) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt141_west, advanceAt141_southWest, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt141_southWest, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case106.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case106, memberCase106, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame106.bindings p
        intro binding member
        simp only [frame106, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h141
        · exact h166
        · exact h167
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt141_west, advanceAt141_southWest, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt141_southWest, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h140 : p 140 with
      | false =>
        cases h166 : p 166 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southWest = some (.walk 166) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt141_west, advanceAt141_southWest, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt141_southWest, h140, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case107.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case107, memberCase107, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame107.bindings p
          intro binding member
          simp only [frame107, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h140
          · exact h141
          · exact h166
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt141_west, advanceAt141_southWest, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt141_southWest, h140, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt141_west, advanceAt141_southWest, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt141_southWest, h140, h141, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 141 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt141_west, advanceAt141_southWest, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt141_southWest, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover160 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .north = some outcome) : OracleCovered rowCases160 p outcome := by
  cases h142 : p 142 with
  | false =>
    cases h116 : p 116 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .north = some (.walk 116) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt116_north, advanceAt116_south, advanceAt142_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_north, h116, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case108.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case108, memberCase108, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame108.bindings p
      intro binding member
      simp only [frame108, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h116
      · exact h142
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt116_north, advanceAt116_south, advanceAt142_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_north, h116, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt116_north, advanceAt116_south, advanceAt142_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_north, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover161 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .south = some outcome) : OracleCovered rowCases161 p outcome := by
  cases h142 : p 142 with
  | false =>
    cases h168 : p 168 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .south = some (.walk 168) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt168_north, advanceAt168_south, advanceAt194_south, advanceAt220_south, advanceAt246_south, advanceAt272_south, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt142_south, h142, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case109.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case109, memberCase109, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame109.bindings p
      intro binding member
      simp only [frame109, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h142
      · exact h168
    | true =>
      cases h194 : p 194 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .south = some (.push 168 (.stay 194)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt168_north, advanceAt168_south, advanceAt194_south, advanceAt220_south, advanceAt246_south, advanceAt272_south, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt142_south, h142, h168, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case719.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case719, memberCase719, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame719.bindings p
        intro binding member
        simp only [frame719, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h142
        · exact h168
        · exact h194
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt168_north, advanceAt168_south, advanceAt194_south, advanceAt220_south, advanceAt246_south, advanceAt272_south, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt142_south, h142, h168, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt168_north, advanceAt168_south, advanceAt194_south, advanceAt220_south, advanceAt246_south, advanceAt272_south, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt142_south, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover162 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .east = some outcome) : OracleCovered rowCases162 p outcome := by
  cases h142 : p 142 with
  | false =>
    cases h143 : p 143 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .east = some (.walk 143) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_east, advanceAt143_east, advanceAt143_west, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt142_east, h142, h143, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case110.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case110, memberCase110, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame110.bindings p
      intro binding member
      simp only [frame110, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h142
      · exact h143
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_east, advanceAt143_east, advanceAt143_west, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt142_east, h142, h143, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_east, advanceAt143_east, advanceAt143_west, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt142_east, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover163 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .west = some outcome) : OracleCovered rowCases163 p outcome := by
  cases h142 : p 142 with
  | false =>
    cases h141 : p 141 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .west = some (.walk 141) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_west, advanceAt140_west, advanceAt141_east, advanceAt141_west, advanceAt142_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_west, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case111.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case111, memberCase111, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame111.bindings p
      intro binding member
      simp only [frame111, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h141
      · exact h142
    | true =>
      cases h140 : p 140 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .west = some (.push 141 (.stay 140)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_west, advanceAt140_west, advanceAt141_east, advanceAt141_west, advanceAt142_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_west, h140, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case691.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case691, memberCase691, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame691.bindings p
        intro binding member
        simp only [frame691, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h140
        · exact h141
        · exact h142
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_west, advanceAt140_west, advanceAt141_east, advanceAt141_west, advanceAt142_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_west, h140, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_west, advanceAt140_west, advanceAt141_east, advanceAt141_west, advanceAt142_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_west, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover164 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northEast = some outcome) : OracleCovered rowCases164 p outcome := by
  cases h142 : p 142 with
  | false =>
    cases h116 : p 116 with
    | false =>
      cases h117 : p 117 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northEast = some (.walk 117) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_north, advanceAt142_east, advanceAt142_northEast, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt142_northEast, h116, h117, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case112.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case112, memberCase112, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame112.bindings p
        intro binding member
        simp only [frame112, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h116
        · exact h117
        · exact h142
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_north, advanceAt142_east, advanceAt142_northEast, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt142_northEast, h116, h117, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h143 : p 143 with
      | false =>
        cases h117 : p 117 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northEast = some (.walk 117) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_north, advanceAt142_east, advanceAt142_northEast, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt142_northEast, h116, h117, h142, h143, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case113.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case113, memberCase113, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame113.bindings p
          intro binding member
          simp only [frame113, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h117
          · exact h142
          · exact h143
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_north, advanceAt142_east, advanceAt142_northEast, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt142_northEast, h116, h117, h142, h143, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_north, advanceAt142_east, advanceAt142_northEast, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt142_northEast, h116, h142, h143, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_north, advanceAt142_east, advanceAt142_northEast, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt142_northEast, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover165 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northWest = some outcome) : OracleCovered rowCases165 p outcome := by
  cases h142 : p 142 with
  | false =>
    cases h116 : p 116 with
    | false =>
      cases h115 : p 115 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northWest = some (.walk 115) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_north, advanceAt142_west, advanceAt142_northWest, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_northWest, h115, h116, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case114.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case114, memberCase114, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame114.bindings p
        intro binding member
        simp only [frame114, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h115
        · exact h116
        · exact h142
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_north, advanceAt142_west, advanceAt142_northWest, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_northWest, h115, h116, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h141 : p 141 with
      | false =>
        cases h115 : p 115 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northWest = some (.walk 115) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_north, advanceAt142_west, advanceAt142_northWest, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_northWest, h115, h116, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case115.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case115, memberCase115, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame115.bindings p
          intro binding member
          simp only [frame115, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h115
          · exact h141
          · exact h142
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_north, advanceAt142_west, advanceAt142_northWest, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_northWest, h115, h116, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_north, advanceAt142_west, advanceAt142_northWest, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_northWest, h116, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_north, advanceAt142_west, advanceAt142_northWest, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt142_northWest, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover166 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southEast = some outcome) : OracleCovered rowCases166 p outcome := by
  cases h142 : p 142 with
  | false =>
    cases h168 : p 168 with
    | false =>
      cases h169 : p 169 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southEast = some (.walk 169) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt142_east, advanceAt142_southEast, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt142_southEast, h142, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case116.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case116, memberCase116, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame116.bindings p
        intro binding member
        simp only [frame116, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h142
        · exact h168
        · exact h169
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt142_east, advanceAt142_southEast, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt142_southEast, h142, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h143 : p 143 with
      | false =>
        cases h169 : p 169 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southEast = some (.walk 169) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt142_east, advanceAt142_southEast, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt142_southEast, h142, h143, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case117.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case117, memberCase117, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame117.bindings p
          intro binding member
          simp only [frame117, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h142
          · exact h143
          · exact h169
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt142_east, advanceAt142_southEast, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt142_southEast, h142, h143, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt142_east, advanceAt142_southEast, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt142_southEast, h142, h143, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt142_east, advanceAt142_southEast, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt142_southEast, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover167 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southWest = some outcome) : OracleCovered rowCases167 p outcome := by
  cases h142 : p 142 with
  | false =>
    cases h168 : p 168 with
    | false =>
      cases h167 : p 167 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southWest = some (.walk 167) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt142_west, advanceAt142_southWest, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt142_southWest, h142, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case118.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case118, memberCase118, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame118.bindings p
        intro binding member
        simp only [frame118, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h142
        · exact h167
        · exact h168
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt142_west, advanceAt142_southWest, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt142_southWest, h142, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h141 : p 141 with
      | false =>
        cases h167 : p 167 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southWest = some (.walk 167) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt142_west, advanceAt142_southWest, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt142_southWest, h141, h142, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case119.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case119, memberCase119, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame119.bindings p
          intro binding member
          simp only [frame119, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h141
          · exact h142
          · exact h167
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt142_west, advanceAt142_southWest, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt142_southWest, h141, h142, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt142_west, advanceAt142_southWest, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt142_southWest, h141, h142, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 142 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt142_south, advanceAt142_west, advanceAt142_southWest, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt142_southWest, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P01
