import NetHack.Soko12Forward220.Unified.P01.OracleCover06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover84 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .northEast = some outcome) : OracleCovered rowCases84 p outcome := by
  cases h115 : p 115 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_north, advanceAt115_east, advanceAt115_northEast, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, cornerAt115_northEast, h115, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_north, advanceAt115_east, advanceAt115_northEast, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, cornerAt115_northEast, h115, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover85 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .northWest = some outcome) : OracleCovered rowCases85 p outcome := by
  cases h115 : p 115 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_north, advanceAt115_west, advanceAt115_northWest, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, cornerAt115_northWest, h115, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_north, advanceAt115_west, advanceAt115_northWest, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, cornerAt115_northWest, h115, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover86 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .southEast = some outcome) : OracleCovered rowCases86 p outcome := by
  cases h115 : p 115 with
  | false =>
    cases h141 : p 141 with
    | false =>
      cases h142 : p 142 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .southEast = some (.walk 142) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_south, advanceAt115_east, advanceAt115_southEast, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt115_southEast, h115, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case040.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case040, memberCase040, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame040.bindings p
        intro binding member
        simp only [frame040, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h115
        · exact h141
        · exact h142
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_south, advanceAt115_east, advanceAt115_southEast, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt115_southEast, h115, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h116 : p 116 with
      | false =>
        cases h142 : p 142 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .southEast = some (.walk 142) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_south, advanceAt115_east, advanceAt115_southEast, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt115_southEast, h115, h116, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case041.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case041, memberCase041, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame041.bindings p
          intro binding member
          simp only [frame041, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h115
          · exact h116
          · exact h142
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_south, advanceAt115_east, advanceAt115_southEast, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt115_southEast, h115, h116, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_south, advanceAt115_east, advanceAt115_southEast, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt115_southEast, h115, h116, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_south, advanceAt115_east, advanceAt115_southEast, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt115_southEast, h115, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover87 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .southWest = some outcome) : OracleCovered rowCases87 p outcome := by
  cases h115 : p 115 with
  | false =>
    cases h141 : p 141 with
    | false =>
      cases h140 : p 140 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .southWest = some (.walk 140) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_south, advanceAt115_west, advanceAt115_southWest, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt115_southWest, h115, h140, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case042.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case042, memberCase042, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame042.bindings p
        intro binding member
        simp only [frame042, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h115
        · exact h140
        · exact h141
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_south, advanceAt115_west, advanceAt115_southWest, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt115_southWest, h115, h140, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_south, advanceAt115_west, advanceAt115_southWest, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt115_southWest, h115, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 115 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt115_south, advanceAt115_west, advanceAt115_southWest, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt115_southWest, h115, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover88 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .north = some outcome) : OracleCovered rowCases88 p outcome := by
  cases h116 : p 116 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt90_south, advanceAt116_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, cornerAt116_north, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt38_north, advanceAt64_north, advanceAt90_north, advanceAt90_south, advanceAt116_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, cornerAt116_north, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover89 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .south = some outcome) : OracleCovered rowCases89 p outcome := by
  cases h116 : p 116 with
  | false =>
    cases h142 : p 142 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .south = some (.walk 142) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt142_north, advanceAt142_south, advanceAt168_south, advanceAt194_south, advanceAt220_south, advanceAt246_south, advanceAt272_south, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt116_south, h116, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case043.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case043, memberCase043, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame043.bindings p
      intro binding member
      simp only [frame043, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h116
      · exact h142
    | true =>
      cases h168 : p 168 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .south = some (.push 142 (.stay 168)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt142_north, advanceAt142_south, advanceAt168_south, advanceAt194_south, advanceAt220_south, advanceAt246_south, advanceAt272_south, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt116_south, h116, h142, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case693.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case693, memberCase693, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame693.bindings p
        intro binding member
        simp only [frame693, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h116
        · exact h142
        · exact h168
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt142_north, advanceAt142_south, advanceAt168_south, advanceAt194_south, advanceAt220_south, advanceAt246_south, advanceAt272_south, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt116_south, h116, h142, h168, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt142_north, advanceAt142_south, advanceAt168_south, advanceAt194_south, advanceAt220_south, advanceAt246_south, advanceAt272_south, advanceAt298_south, advanceAt324_south, advanceAt350_south, advanceAt376_south, advanceAt402_south, advanceAt428_south, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt428, doorAt428, trapAt428, boxAt428, holeAt428, cornerAt116_south, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover90 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .east = some outcome) : OracleCovered rowCases90 p outcome := by
  cases h116 : p 116 with
  | false =>
    cases h117 : p 117 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .east = some (.walk 117) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_east, advanceAt117_east, advanceAt117_west, advanceAt118_east, advanceAt119_east, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, cornerAt116_east, h116, h117, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case044.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case044, memberCase044, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame044.bindings p
      intro binding member
      simp only [frame044, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h116
      · exact h117
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_east, advanceAt117_east, advanceAt117_west, advanceAt118_east, advanceAt119_east, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, cornerAt116_east, h116, h117, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_east, advanceAt117_east, advanceAt117_west, advanceAt118_east, advanceAt119_east, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, cornerAt116_east, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover91 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .west = some outcome) : OracleCovered rowCases91 p outcome := by
  cases h116 : p 116 with
  | false =>
    cases h115 : p 115 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .west = some (.walk 115) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_west, advanceAt105_west, advanceAt106_west, advanceAt107_west, advanceAt108_west, advanceAt109_west, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_east, advanceAt115_west, advanceAt116_west, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, cornerAt116_west, h115, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case045.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case045, memberCase045, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame045.bindings p
      intro binding member
      simp only [frame045, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h115
      · exact h116
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_west, advanceAt105_west, advanceAt106_west, advanceAt107_west, advanceAt108_west, advanceAt109_west, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_east, advanceAt115_west, advanceAt116_west, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, cornerAt116_west, h115, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_west, advanceAt105_west, advanceAt106_west, advanceAt107_west, advanceAt108_west, advanceAt109_west, advanceAt110_west, advanceAt111_west, advanceAt112_west, advanceAt113_west, advanceAt114_west, advanceAt115_east, advanceAt115_west, advanceAt116_west, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, cornerAt116_west, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover92 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .northEast = some outcome) : OracleCovered rowCases92 p outcome := by
  cases h116 : p 116 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_north, advanceAt116_east, advanceAt116_northEast, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, cornerAt116_northEast, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_north, advanceAt116_east, advanceAt116_northEast, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, cornerAt116_northEast, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover93 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .northWest = some outcome) : OracleCovered rowCases93 p outcome := by
  cases h116 : p 116 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_north, advanceAt116_west, advanceAt116_northWest, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, cornerAt116_northWest, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_north, advanceAt116_west, advanceAt116_northWest, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, cornerAt116_northWest, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover94 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southEast = some outcome) : OracleCovered rowCases94 p outcome := by
  cases h116 : p 116 with
  | false =>
    cases h142 : p 142 with
    | false =>
      cases h143 : p 143 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southEast = some (.walk 143) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt116_east, advanceAt116_southEast, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt116_southEast, h116, h142, h143, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case046.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case046, memberCase046, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame046.bindings p
        intro binding member
        simp only [frame046, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h116
        · exact h142
        · exact h143
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt116_east, advanceAt116_southEast, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt116_southEast, h116, h142, h143, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h117 : p 117 with
      | false =>
        cases h143 : p 143 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southEast = some (.walk 143) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt116_east, advanceAt116_southEast, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt116_southEast, h116, h117, h142, h143, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case047.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case047, memberCase047, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame047.bindings p
          intro binding member
          simp only [frame047, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h116
          · exact h117
          · exact h143
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt116_east, advanceAt116_southEast, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt116_southEast, h116, h117, h142, h143, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt116_east, advanceAt116_southEast, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt116_southEast, h116, h117, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt116_east, advanceAt116_southEast, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, cornerAt116_southEast, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover95 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southWest = some outcome) : OracleCovered rowCases95 p outcome := by
  cases h116 : p 116 with
  | false =>
    cases h142 : p 142 with
    | false =>
      cases h141 : p 141 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southWest = some (.walk 141) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt116_west, advanceAt116_southWest, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt116_southWest, h116, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case048.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case048, memberCase048, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame048.bindings p
        intro binding member
        simp only [frame048, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h116
        · exact h141
        · exact h142
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt116_west, advanceAt116_southWest, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt116_southWest, h116, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h115 : p 115 with
      | false =>
        cases h141 : p 141 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southWest = some (.walk 141) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt116_west, advanceAt116_southWest, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt116_southWest, h115, h116, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case049.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case049, memberCase049, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame049.bindings p
          intro binding member
          simp only [frame049, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h115
          · exact h116
          · exact h141
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt116_west, advanceAt116_southWest, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt116_southWest, h115, h116, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt116_west, advanceAt116_southWest, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt116_southWest, h115, h116, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 116 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt116_south, advanceAt116_west, advanceAt116_southWest, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, cornerAt116_southWest, h116, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P01
