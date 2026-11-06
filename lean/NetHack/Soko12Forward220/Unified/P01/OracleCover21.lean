import NetHack.Soko12Forward220.Unified.P01.OracleCover20
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover252 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northEast = some outcome) : OracleCovered rowCases252 p outcome := by
  cases h168 : p 168 with
  | false =>
    cases h142 : p 142 with
    | false =>
      cases h143 : p 143 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northEast = some (.walk 143) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_north, advanceAt168_east, advanceAt168_northEast, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt168_northEast, h142, h143, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case206.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case206, memberCase206, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame206.bindings p
        intro binding member
        simp only [frame206, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h142
        · exact h143
        · exact h168
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_north, advanceAt168_east, advanceAt168_northEast, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt168_northEast, h142, h143, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h169 : p 169 with
      | false =>
        cases h143 : p 143 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northEast = some (.walk 143) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_north, advanceAt168_east, advanceAt168_northEast, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt168_northEast, h142, h143, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case207.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case207, memberCase207, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame207.bindings p
          intro binding member
          simp only [frame207, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h143
          · exact h168
          · exact h169
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_north, advanceAt168_east, advanceAt168_northEast, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt168_northEast, h142, h143, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_north, advanceAt168_east, advanceAt168_northEast, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt168_northEast, h142, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_north, advanceAt168_east, advanceAt168_northEast, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt168_northEast, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover253 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northWest = some outcome) : OracleCovered rowCases253 p outcome := by
  cases h168 : p 168 with
  | false =>
    cases h142 : p 142 with
    | false =>
      cases h141 : p 141 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northWest = some (.walk 141) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_north, advanceAt168_west, advanceAt168_northWest, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt168_northWest, h141, h142, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case208.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case208, memberCase208, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame208.bindings p
        intro binding member
        simp only [frame208, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h141
        · exact h142
        · exact h168
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_north, advanceAt168_west, advanceAt168_northWest, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt168_northWest, h141, h142, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h167 : p 167 with
      | false =>
        cases h141 : p 141 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northWest = some (.walk 141) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_north, advanceAt168_west, advanceAt168_northWest, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt168_northWest, h141, h142, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case209.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case209, memberCase209, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame209.bindings p
          intro binding member
          simp only [frame209, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h141
          · exact h167
          · exact h168
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_north, advanceAt168_west, advanceAt168_northWest, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt168_northWest, h141, h142, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_north, advanceAt168_west, advanceAt168_northWest, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt168_northWest, h142, h167, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_north, advanceAt168_west, advanceAt168_northWest, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, cornerAt168_northWest, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover254 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .southEast = some outcome) : OracleCovered rowCases254 p outcome := by
  cases h168 : p 168 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_south, advanceAt168_east, advanceAt168_southEast, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, cornerAt168_southEast, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_south, advanceAt168_east, advanceAt168_southEast, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, cornerAt168_southEast, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover255 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .southWest = some outcome) : OracleCovered rowCases255 p outcome := by
  cases h168 : p 168 with
  | false =>
    cases h194 : p 194 with
    | false =>
      cases h193 : p 193 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .southWest = some (.walk 193) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_south, advanceAt168_west, advanceAt168_southWest, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, cornerAt168_southWest, h168, h193, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case210.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case210, memberCase210, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame210.bindings p
        intro binding member
        simp only [frame210, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h168
        · exact h193
        · exact h194
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_south, advanceAt168_west, advanceAt168_southWest, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, cornerAt168_southWest, h168, h193, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h167 : p 167 with
      | false =>
        cases h193 : p 193 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .southWest = some (.walk 193) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_south, advanceAt168_west, advanceAt168_southWest, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, cornerAt168_southWest, h167, h168, h193, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case211.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case211, memberCase211, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame211.bindings p
          intro binding member
          simp only [frame211, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h167
          · exact h168
          · exact h193
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_south, advanceAt168_west, advanceAt168_southWest, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, cornerAt168_southWest, h167, h168, h193, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_south, advanceAt168_west, advanceAt168_southWest, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, cornerAt168_southWest, h167, h168, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 168 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt168_south, advanceAt168_west, advanceAt168_southWest, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, cornerAt168_southWest, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover256 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .north = some outcome) : OracleCovered rowCases256 p outcome := by
  cases h169 : p 169 with
  | false =>
    cases h143 : p 143 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .north = some (.walk 143) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt13_north, advanceAt39_north, advanceAt65_north, advanceAt91_north, advanceAt117_north, advanceAt143_north, advanceAt143_south, advanceAt169_north, floorAt13, doorAt13, trapAt13, boxAt13, holeAt13, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_north, h143, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case212.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case212, memberCase212, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame212.bindings p
      intro binding member
      simp only [frame212, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h143
      · exact h169
    | true =>
      cases h117 : p 117 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .north = some (.push 143 (.stay 117)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt13_north, advanceAt39_north, advanceAt65_north, advanceAt91_north, advanceAt117_north, advanceAt143_north, advanceAt143_south, advanceAt169_north, floorAt13, doorAt13, trapAt13, boxAt13, holeAt13, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_north, h117, h143, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case696.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case696, memberCase696, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame696.bindings p
        intro binding member
        simp only [frame696, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h117
        · exact h143
        · exact h169
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt13_north, advanceAt39_north, advanceAt65_north, advanceAt91_north, advanceAt117_north, advanceAt143_north, advanceAt143_south, advanceAt169_north, floorAt13, doorAt13, trapAt13, boxAt13, holeAt13, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_north, h117, h143, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt13_north, advanceAt39_north, advanceAt65_north, advanceAt91_north, advanceAt117_north, advanceAt143_north, advanceAt143_south, advanceAt169_north, floorAt13, doorAt13, trapAt13, boxAt13, holeAt13, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_north, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover257 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .south = some outcome) : OracleCovered rowCases257 p outcome := by
  cases h169 : p 169 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_south, advanceAt195_north, advanceAt195_south, advanceAt221_south, advanceAt247_south, advanceAt273_south, advanceAt299_south, advanceAt325_south, advanceAt351_south, advanceAt377_south, advanceAt403_south, advanceAt429_south, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt351, doorAt351, trapAt351, boxAt351, holeAt351, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt403, doorAt403, trapAt403, boxAt403, holeAt403, floorAt429, doorAt429, trapAt429, boxAt429, holeAt429, cornerAt169_south, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_south, advanceAt195_north, advanceAt195_south, advanceAt221_south, advanceAt247_south, advanceAt273_south, advanceAt299_south, advanceAt325_south, advanceAt351_south, advanceAt377_south, advanceAt403_south, advanceAt429_south, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt351, doorAt351, trapAt351, boxAt351, holeAt351, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt403, doorAt403, trapAt403, boxAt403, holeAt403, floorAt429, doorAt429, trapAt429, boxAt429, holeAt429, cornerAt169_south, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover258 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .east = some outcome) : OracleCovered rowCases258 p outcome := by
  cases h169 : p 169 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_east, advanceAt170_east, advanceAt170_west, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt169_east, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_east, advanceAt170_east, advanceAt170_west, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt169_east, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover259 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .west = some outcome) : OracleCovered rowCases259 p outcome := by
  cases h169 : p 169 with
  | false =>
    cases h168 : p 168 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .west = some (.walk 168) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_west, advanceAt161_west, advanceAt162_west, advanceAt163_west, advanceAt164_west, advanceAt165_west, advanceAt166_west, advanceAt167_west, advanceAt168_east, advanceAt168_west, advanceAt169_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_west, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case213.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case213, memberCase213, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame213.bindings p
      intro binding member
      simp only [frame213, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h168
      · exact h169
    | true =>
      cases h167 : p 167 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .west = some (.push 168 (.stay 167)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_west, advanceAt161_west, advanceAt162_west, advanceAt163_west, advanceAt164_west, advanceAt165_west, advanceAt166_west, advanceAt167_west, advanceAt168_east, advanceAt168_west, advanceAt169_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_west, h167, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case721.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case721, memberCase721, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame721.bindings p
        intro binding member
        simp only [frame721, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h167
        · exact h168
        · exact h169
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_west, advanceAt161_west, advanceAt162_west, advanceAt163_west, advanceAt164_west, advanceAt165_west, advanceAt166_west, advanceAt167_west, advanceAt168_east, advanceAt168_west, advanceAt169_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_west, h167, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_west, advanceAt161_west, advanceAt162_west, advanceAt163_west, advanceAt164_west, advanceAt165_west, advanceAt166_west, advanceAt167_west, advanceAt168_east, advanceAt168_west, advanceAt169_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_west, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover260 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .northEast = some outcome) : OracleCovered rowCases260 p outcome := by
  cases h169 : p 169 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_north, advanceAt169_east, advanceAt169_northEast, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, cornerAt169_northEast, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_north, advanceAt169_east, advanceAt169_northEast, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, cornerAt169_northEast, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover261 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .northWest = some outcome) : OracleCovered rowCases261 p outcome := by
  cases h169 : p 169 with
  | false =>
    cases h143 : p 143 with
    | false =>
      cases h142 : p 142 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .northWest = some (.walk 142) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_north, advanceAt169_west, advanceAt169_northWest, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_northWest, h142, h143, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case214.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case214, memberCase214, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame214.bindings p
        intro binding member
        simp only [frame214, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h142
        · exact h143
        · exact h169
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_north, advanceAt169_west, advanceAt169_northWest, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_northWest, h142, h143, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h168 : p 168 with
      | false =>
        cases h142 : p 142 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .northWest = some (.walk 142) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_north, advanceAt169_west, advanceAt169_northWest, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_northWest, h142, h143, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case215.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case215, memberCase215, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame215.bindings p
          intro binding member
          simp only [frame215, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h142
          · exact h168
          · exact h169
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_north, advanceAt169_west, advanceAt169_northWest, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_northWest, h142, h143, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_north, advanceAt169_west, advanceAt169_northWest, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_northWest, h143, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_north, advanceAt169_west, advanceAt169_northWest, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, cornerAt169_northWest, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover262 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .southEast = some outcome) : OracleCovered rowCases262 p outcome := by
  cases h169 : p 169 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_south, advanceAt169_east, advanceAt169_southEast, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, cornerAt169_southEast, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_south, advanceAt169_east, advanceAt169_southEast, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, cornerAt169_southEast, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover263 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .southWest = some outcome) : OracleCovered rowCases263 p outcome := by
  cases h169 : p 169 with
  | false =>
    cases h168 : p 168 with
    | false =>
      cases h194 : p 194 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .southWest = some (.walk 194) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_south, advanceAt169_west, advanceAt169_southWest, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, cornerAt169_southWest, h168, h169, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case216.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case216, memberCase216, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame216.bindings p
        intro binding member
        simp only [frame216, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h168
        · exact h169
        · exact h194
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_south, advanceAt169_west, advanceAt169_southWest, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, cornerAt169_southWest, h168, h169, h194, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_south, advanceAt169_west, advanceAt169_southWest, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, cornerAt169_southWest, h168, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 169 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt169_south, advanceAt169_west, advanceAt169_southWest, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, cornerAt169_southWest, h169, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P01
