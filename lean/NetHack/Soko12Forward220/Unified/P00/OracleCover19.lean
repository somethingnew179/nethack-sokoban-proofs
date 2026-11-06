import NetHack.Soko12Forward220.Unified.P00.OracleCover18
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover228 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .northEast = some outcome) : OracleCovered rowCases228 p outcome := by
  cases h166 : p 166 with
  | false =>
    cases h140 : p 140 with
    | false =>
      cases h141 : p 141 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .northEast = some (.walk 141) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_north, advanceAt166_east, advanceAt166_northEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt166_northEast, h140, h141, h166, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case183.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case183, memberCase183, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame183.bindings p
        intro binding member
        simp only [frame183, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h140
        · exact h141
        · exact h166
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_north, advanceAt166_east, advanceAt166_northEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt166_northEast, h140, h141, h166, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h167 : p 167 with
      | false =>
        cases h141 : p 141 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .northEast = some (.walk 141) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_north, advanceAt166_east, advanceAt166_northEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt166_northEast, h140, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case184.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case184, memberCase184, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame184.bindings p
          intro binding member
          simp only [frame184, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h141
          · exact h166
          · exact h167
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_north, advanceAt166_east, advanceAt166_northEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt166_northEast, h140, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_north, advanceAt166_east, advanceAt166_northEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt166_northEast, h140, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_north, advanceAt166_east, advanceAt166_northEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt166_northEast, h166, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover229 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .northWest = some outcome) : OracleCovered rowCases229 p outcome := by
  cases h166 : p 166 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_north, advanceAt166_west, advanceAt166_northWest, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, cornerAt166_northWest, h166, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_north, advanceAt166_west, advanceAt166_northWest, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, cornerAt166_northWest, h166, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover230 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .southEast = some outcome) : OracleCovered rowCases230 p outcome := by
  cases h166 : p 166 with
  | false =>
    cases h192 : p 192 with
    | false =>
      cases h193 : p 193 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .southEast = some (.walk 193) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_south, advanceAt166_east, advanceAt166_southEast, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, cornerAt166_southEast, h166, h192, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case185.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case185, memberCase185, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame185.bindings p
        intro binding member
        simp only [frame185, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h166
        · exact h192
        · exact h193
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_south, advanceAt166_east, advanceAt166_southEast, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, cornerAt166_southEast, h166, h192, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h167 : p 167 with
      | false =>
        cases h193 : p 193 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .southEast = some (.walk 193) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_south, advanceAt166_east, advanceAt166_southEast, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, cornerAt166_southEast, h166, h167, h192, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case186.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case186, memberCase186, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame186.bindings p
          intro binding member
          simp only [frame186, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h166
          · exact h167
          · exact h193
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_south, advanceAt166_east, advanceAt166_southEast, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, cornerAt166_southEast, h166, h167, h192, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_south, advanceAt166_east, advanceAt166_southEast, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, cornerAt166_southEast, h166, h167, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_south, advanceAt166_east, advanceAt166_southEast, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, cornerAt166_southEast, h166, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover231 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .southWest = some outcome) : OracleCovered rowCases231 p outcome := by
  cases h166 : p 166 with
  | false =>
    cases h192 : p 192 with
    | false =>
      cases h191 : p 191 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .southWest = some (.walk 191) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_south, advanceAt166_west, advanceAt166_southWest, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, cornerAt166_southWest, h166, h191, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case187.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case187, memberCase187, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame187.bindings p
        intro binding member
        simp only [frame187, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h166
        · exact h191
        · exact h192
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_south, advanceAt166_west, advanceAt166_southWest, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, cornerAt166_southWest, h166, h191, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_south, advanceAt166_west, advanceAt166_southWest, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, cornerAt166_southWest, h166, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 166 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt166_south, advanceAt166_west, advanceAt166_southWest, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, cornerAt166_southWest, h166, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover232 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .north = some outcome) : OracleCovered rowCases232 p outcome := by
  cases h167 : p 167 with
  | false =>
    cases h141 : p 141 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .north = some (.walk 141) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt141_south, advanceAt167_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_north, h141, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case188.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case188, memberCase188, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame188.bindings p
      intro binding member
      simp only [frame188, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h141
      · exact h167
    | true =>
      cases h115 : p 115 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .north = some (.push 141 (.stay 115)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt141_south, advanceAt167_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_north, h115, h141, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case686.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case686, memberCase686, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame686.bindings p
        intro binding member
        simp only [frame686, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h115
        · exact h141
        · exact h167
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt141_south, advanceAt167_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_north, h115, h141, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt141_south, advanceAt167_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_north, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover233 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .south = some outcome) : OracleCovered rowCases233 p outcome := by
  cases h167 : p 167 with
  | false =>
    cases h193 : p 193 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .south = some (.walk 193) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt193_north, advanceAt193_south, advanceAt219_south, advanceAt245_south, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt167_south, h167, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case189.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case189, memberCase189, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame189.bindings p
      intro binding member
      simp only [frame189, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h167
      · exact h193
    | true =>
      cases h219 : p 219 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .south = some (.push 193 (.stay 219)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt193_north, advanceAt193_south, advanceAt219_south, advanceAt245_south, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt167_south, h167, h193, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case745.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case745, memberCase745, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame745.bindings p
        intro binding member
        simp only [frame745, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h167
        · exact h193
        · exact h219
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt193_north, advanceAt193_south, advanceAt219_south, advanceAt245_south, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt167_south, h167, h193, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt193_north, advanceAt193_south, advanceAt219_south, advanceAt245_south, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt167_south, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover234 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .east = some outcome) : OracleCovered rowCases234 p outcome := by
  cases h167 : p 167 with
  | false =>
    cases h168 : p 168 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .east = some (.walk 168) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_east, advanceAt168_east, advanceAt168_west, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt167_east, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case190.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case190, memberCase190, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame190.bindings p
      intro binding member
      simp only [frame190, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h167
      · exact h168
    | true =>
      cases h169 : p 169 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .east = some (.push 168 (.stay 169)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_east, advanceAt168_east, advanceAt168_west, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt167_east, h167, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case718.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case718, memberCase718, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame718.bindings p
        intro binding member
        simp only [frame718, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h167
        · exact h168
        · exact h169
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_east, advanceAt168_east, advanceAt168_west, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt167_east, h167, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_east, advanceAt168_east, advanceAt168_west, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt167_east, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover235 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .west = some outcome) : OracleCovered rowCases235 p outcome := by
  cases h167 : p 167 with
  | false =>
    cases h166 : p 166 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .west = some (.walk 166) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_west, advanceAt161_west, advanceAt162_west, advanceAt163_west, advanceAt164_west, advanceAt165_west, advanceAt166_east, advanceAt166_west, advanceAt167_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_west, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case191.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case191, memberCase191, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame191.bindings p
      intro binding member
      simp only [frame191, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h166
      · exact h167
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_west, advanceAt161_west, advanceAt162_west, advanceAt163_west, advanceAt164_west, advanceAt165_west, advanceAt166_east, advanceAt166_west, advanceAt167_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_west, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_west, advanceAt161_west, advanceAt162_west, advanceAt163_west, advanceAt164_west, advanceAt165_west, advanceAt166_east, advanceAt166_west, advanceAt167_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_west, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover236 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northEast = some outcome) : OracleCovered rowCases236 p outcome := by
  cases h167 : p 167 with
  | false =>
    cases h141 : p 141 with
    | false =>
      cases h142 : p 142 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northEast = some (.walk 142) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_north, advanceAt167_east, advanceAt167_northEast, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt167_northEast, h141, h142, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case192.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case192, memberCase192, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame192.bindings p
        intro binding member
        simp only [frame192, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h141
        · exact h142
        · exact h167
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_north, advanceAt167_east, advanceAt167_northEast, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt167_northEast, h141, h142, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h168 : p 168 with
      | false =>
        cases h142 : p 142 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northEast = some (.walk 142) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_north, advanceAt167_east, advanceAt167_northEast, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt167_northEast, h141, h142, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case193.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case193, memberCase193, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame193.bindings p
          intro binding member
          simp only [frame193, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h142
          · exact h167
          · exact h168
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_north, advanceAt167_east, advanceAt167_northEast, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt167_northEast, h141, h142, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_north, advanceAt167_east, advanceAt167_northEast, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt167_northEast, h141, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_north, advanceAt167_east, advanceAt167_northEast, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt167_northEast, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover237 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northWest = some outcome) : OracleCovered rowCases237 p outcome := by
  cases h167 : p 167 with
  | false =>
    cases h141 : p 141 with
    | false =>
      cases h140 : p 140 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northWest = some (.walk 140) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_north, advanceAt167_west, advanceAt167_northWest, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_northWest, h140, h141, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case194.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case194, memberCase194, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame194.bindings p
        intro binding member
        simp only [frame194, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h140
        · exact h141
        · exact h167
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_north, advanceAt167_west, advanceAt167_northWest, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_northWest, h140, h141, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h166 : p 166 with
      | false =>
        cases h140 : p 140 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northWest = some (.walk 140) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_north, advanceAt167_west, advanceAt167_northWest, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_northWest, h140, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case195.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case195, memberCase195, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame195.bindings p
          intro binding member
          simp only [frame195, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h140
          · exact h166
          · exact h167
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_north, advanceAt167_west, advanceAt167_northWest, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_northWest, h140, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_north, advanceAt167_west, advanceAt167_northWest, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_northWest, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_north, advanceAt167_west, advanceAt167_northWest, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt167_northWest, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover238 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southEast = some outcome) : OracleCovered rowCases238 p outcome := by
  cases h167 : p 167 with
  | false =>
    cases h193 : p 193 with
    | false =>
      cases h194 : p 194 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southEast = some (.walk 194) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt167_east, advanceAt167_southEast, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, cornerAt167_southEast, h167, h193, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case196.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case196, memberCase196, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame196.bindings p
        intro binding member
        simp only [frame196, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h167
        · exact h193
        · exact h194
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt167_east, advanceAt167_southEast, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, cornerAt167_southEast, h167, h193, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h168 : p 168 with
      | false =>
        cases h194 : p 194 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southEast = some (.walk 194) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt167_east, advanceAt167_southEast, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, cornerAt167_southEast, h167, h168, h193, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case197.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case197, memberCase197, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame197.bindings p
          intro binding member
          simp only [frame197, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h167
          · exact h168
          · exact h194
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt167_east, advanceAt167_southEast, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, cornerAt167_southEast, h167, h168, h193, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt167_east, advanceAt167_southEast, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, cornerAt167_southEast, h167, h168, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt167_east, advanceAt167_southEast, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, cornerAt167_southEast, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover239 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southWest = some outcome) : OracleCovered rowCases239 p outcome := by
  cases h167 : p 167 with
  | false =>
    cases h193 : p 193 with
    | false =>
      cases h192 : p 192 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southWest = some (.walk 192) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt167_west, advanceAt167_southWest, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, cornerAt167_southWest, h167, h192, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case198.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case198, memberCase198, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame198.bindings p
        intro binding member
        simp only [frame198, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h167
        · exact h192
        · exact h193
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt167_west, advanceAt167_southWest, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, cornerAt167_southWest, h167, h192, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h166 : p 166 with
      | false =>
        cases h192 : p 192 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southWest = some (.walk 192) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt167_west, advanceAt167_southWest, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, cornerAt167_southWest, h166, h167, h192, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case199.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case199, memberCase199, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame199.bindings p
          intro binding member
          simp only [frame199, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h166
          · exact h167
          · exact h192
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt167_west, advanceAt167_southWest, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, cornerAt167_southWest, h166, h167, h192, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt167_west, advanceAt167_southWest, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, cornerAt167_southWest, h166, h167, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 167 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt167_south, advanceAt167_west, advanceAt167_southWest, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, cornerAt167_southWest, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P00
