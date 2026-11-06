import NetHack.Soko12Forward220.Unified.P05.OracleCover52
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover636 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .northEast = some outcome) : OracleCovered rowCases636 p outcome := by
  cases h294 : p 294 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt294_north, advanceAt294_east, advanceAt294_northEast, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, cornerAt294_northEast, h294, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt294_north, advanceAt294_east, advanceAt294_northEast, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, cornerAt294_northEast, h294, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover637 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .northWest = some outcome) : OracleCovered rowCases637 p outcome := by
  cases h294 : p 294 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt294_north, advanceAt294_west, advanceAt294_northWest, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, cornerAt294_northWest, h294, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt294_north, advanceAt294_west, advanceAt294_northWest, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, cornerAt294_northWest, h294, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover638 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .southEast = some outcome) : OracleCovered rowCases638 p outcome := by
  cases h294 : p 294 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt294_south, advanceAt294_east, advanceAt294_southEast, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, cornerAt294_southEast, h294, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt294_south, advanceAt294_east, advanceAt294_southEast, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, cornerAt294_southEast, h294, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover639 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .southWest = some outcome) : OracleCovered rowCases639 p outcome := by
  cases h294 : p 294 with
  | false =>
    cases h320 : p 320 with
    | false =>
      cases h319 : p 319 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .southWest = some (.walk 319) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt294_south, advanceAt294_west, advanceAt294_southWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt294_southWest, h294, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case582.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case582, memberCase582, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame582.bindings p
        intro binding member
        simp only [frame582, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h294
        · exact h319
        · exact h320
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt294_south, advanceAt294_west, advanceAt294_southWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt294_southWest, h294, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h293 : p 293 with
      | false =>
        cases h319 : p 319 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .southWest = some (.walk 319) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt294_south, advanceAt294_west, advanceAt294_southWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt294_southWest, h293, h294, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case583.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case583, memberCase583, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame583.bindings p
          intro binding member
          simp only [frame583, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h293
          · exact h294
          · exact h319
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt294_south, advanceAt294_west, advanceAt294_southWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt294_southWest, h293, h294, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt294_south, advanceAt294_west, advanceAt294_southWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt294_southWest, h293, h294, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 294 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt294_south, advanceAt294_west, advanceAt294_southWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt294_southWest, h294, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover640 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .north = some outcome) : OracleCovered rowCases640 p outcome := by
  cases h296 : p 296 with
  | false =>
    cases h270 : p 270 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .north = some (.walk 270) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt270_south, advanceAt296_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_north, h270, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case584.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case584, memberCase584, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame584.bindings p
      intro binding member
      simp only [frame584, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h270
      · exact h296
    | true =>
      cases h244 : p 244 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .north = some (.push 270 (.stay 244)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt270_south, advanceAt296_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_north, h244, h270, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case822.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case822, memberCase822, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame822.bindings p
        intro binding member
        simp only [frame822, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h244
        · exact h270
        · exact h296
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt270_south, advanceAt296_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_north, h244, h270, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt270_south, advanceAt296_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_north, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover641 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .south = some outcome) : OracleCovered rowCases641 p outcome := by
  cases h296 : p 296 with
  | false =>
    cases h322 : p 322 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .south = some (.walk 322) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt322_north, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt296_south, h296, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case585.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case585, memberCase585, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame585.bindings p
      intro binding member
      simp only [frame585, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h296
      · exact h322
    | true =>
      cases h348 : p 348 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .south = some (.push 322 (.stay 348)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt322_north, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt296_south, h296, h322, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case849.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case849, memberCase849, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame849.bindings p
        intro binding member
        simp only [frame849, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h296
        · exact h322
        · exact h348
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt322_north, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt296_south, h296, h322, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt322_north, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt296_south, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover642 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .east = some outcome) : OracleCovered rowCases642 p outcome := by
  cases h296 : p 296 with
  | false =>
    cases h297 : p 297 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .east = some (.walk 297) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_east, advanceAt297_east, advanceAt297_west, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt296_east, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case586.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case586, memberCase586, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame586.bindings p
      intro binding member
      simp only [frame586, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h296
      · exact h297
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_east, advanceAt297_east, advanceAt297_west, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt296_east, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_east, advanceAt297_east, advanceAt297_west, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt296_east, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover643 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .west = some outcome) : OracleCovered rowCases643 p outcome := by
  cases h296 : p 296 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_west, advanceAt289_west, advanceAt290_west, advanceAt291_west, advanceAt292_west, advanceAt293_west, advanceAt294_west, advanceAt295_east, advanceAt295_west, advanceAt296_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_west, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_west, advanceAt289_west, advanceAt290_west, advanceAt291_west, advanceAt292_west, advanceAt293_west, advanceAt294_west, advanceAt295_east, advanceAt295_west, advanceAt296_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_west, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover644 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .northEast = some outcome) : OracleCovered rowCases644 p outcome := by
  cases h296 : p 296 with
  | false =>
    cases h270 : p 270 with
    | false =>
      cases h271 : p 271 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .northEast = some (.walk 271) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_east, advanceAt296_northEast, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt296_northEast, h270, h271, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case587.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case587, memberCase587, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame587.bindings p
        intro binding member
        simp only [frame587, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h270
        · exact h271
        · exact h296
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_east, advanceAt296_northEast, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt296_northEast, h270, h271, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h297 : p 297 with
      | false =>
        cases h271 : p 271 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .northEast = some (.walk 271) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_east, advanceAt296_northEast, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt296_northEast, h270, h271, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case588.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case588, memberCase588, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame588.bindings p
          intro binding member
          simp only [frame588, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h271
          · exact h296
          · exact h297
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_east, advanceAt296_northEast, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt296_northEast, h270, h271, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_east, advanceAt296_northEast, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt296_northEast, h270, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_east, advanceAt296_northEast, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt296_northEast, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover645 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .northWest = some outcome) : OracleCovered rowCases645 p outcome := by
  cases h296 : p 296 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_west, advanceAt296_northWest, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_northWest, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_west, advanceAt296_northWest, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_northWest, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover646 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .southEast = some outcome) : OracleCovered rowCases646 p outcome := by
  cases h296 : p 296 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt296_east, advanceAt296_southEast, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, cornerAt296_southEast, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt296_east, advanceAt296_southEast, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, cornerAt296_southEast, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover647 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .southWest = some outcome) : OracleCovered rowCases647 p outcome := by
  cases h296 : p 296 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt296_west, advanceAt296_southWest, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt296_southWest, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 296 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt296_west, advanceAt296_southWest, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt296_southWest, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P05
