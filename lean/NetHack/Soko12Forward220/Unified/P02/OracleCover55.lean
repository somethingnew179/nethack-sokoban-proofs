import NetHack.Soko12Forward220.Unified.P02.OracleCover54
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover660 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .northEast = some outcome) : OracleCovered rowCases660 p outcome := by
  cases h320 : p 320 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_east, advanceAt320_northEast, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, cornerAt320_northEast, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_east, advanceAt320_northEast, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, cornerAt320_northEast, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover661 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .northWest = some outcome) : OracleCovered rowCases661 p outcome := by
  cases h320 : p 320 with
  | false =>
    cases h294 : p 294 with
    | false =>
      cases h293 : p 293 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .northWest = some (.walk 293) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_west, advanceAt320_northWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_northWest, h293, h294, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case612.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case612, memberCase612, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame612.bindings p
        intro binding member
        simp only [frame612, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h293
        · exact h294
        · exact h320
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_west, advanceAt320_northWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_northWest, h293, h294, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h319 : p 319 with
      | false =>
        cases h293 : p 293 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .northWest = some (.walk 293) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_west, advanceAt320_northWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_northWest, h293, h294, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case613.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case613, memberCase613, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame613.bindings p
          intro binding member
          simp only [frame613, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h293
          · exact h319
          · exact h320
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_west, advanceAt320_northWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_northWest, h293, h294, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_west, advanceAt320_northWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_northWest, h294, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_west, advanceAt320_northWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_northWest, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover662 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .southEast = some outcome) : OracleCovered rowCases662 p outcome := by
  cases h320 : p 320 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt320_east, advanceAt320_southEast, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, cornerAt320_southEast, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt320_east, advanceAt320_southEast, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, cornerAt320_southEast, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover663 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .southWest = some outcome) : OracleCovered rowCases663 p outcome := by
  cases h320 : p 320 with
  | false =>
    cases h319 : p 319 with
    | false =>
      cases h345 : p 345 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .southWest = some (.walk 345) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt320_west, advanceAt320_southWest, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt320_southWest, h319, h320, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case614.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case614, memberCase614, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame614.bindings p
        intro binding member
        simp only [frame614, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h319
        · exact h320
        · exact h345
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt320_west, advanceAt320_southWest, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt320_southWest, h319, h320, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt320_west, advanceAt320_southWest, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt320_southWest, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 320 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt320_west, advanceAt320_southWest, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt320_southWest, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover664 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .north = some outcome) : OracleCovered rowCases664 p outcome := by
  cases h322 : p 322 with
  | false =>
    cases h296 : p 296 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .north = some (.walk 296) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt296_south, advanceAt322_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_north, h296, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case615.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case615, memberCase615, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame615.bindings p
      intro binding member
      simp only [frame615, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h296
      · exact h322
    | true =>
      cases h270 : p 270 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .north = some (.push 296 (.stay 270)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt296_south, advanceAt322_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_north, h270, h296, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case834.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case834, memberCase834, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame834.bindings p
        intro binding member
        simp only [frame834, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h270
        · exact h296
        · exact h322
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt296_south, advanceAt322_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_north, h270, h296, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt296_south, advanceAt322_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_north, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover665 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .south = some outcome) : OracleCovered rowCases665 p outcome := by
  cases h322 : p 322 with
  | false =>
    cases h348 : p 348 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .south = some (.walk 348) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_south, advanceAt348_north, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt322_south, h322, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case616.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case616, memberCase616, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame616.bindings p
      intro binding member
      simp only [frame616, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h322
      · exact h348
    | true =>
      cases h374 : p 374 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .south = some (.push 348 (.stay 374)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_south, advanceAt348_north, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt322_south, h322, h348, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case847.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case847, memberCase847, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame847.bindings p
        intro binding member
        simp only [frame847, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h322
        · exact h348
        · exact h374
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_south, advanceAt348_north, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt322_south, h322, h348, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_south, advanceAt348_north, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt322_south, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover666 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .east = some outcome) : OracleCovered rowCases666 p outcome := by
  cases h322 : p 322 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_east, advanceAt323_east, advanceAt323_west, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt322_east, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_east, advanceAt323_east, advanceAt323_west, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt322_east, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover667 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .west = some outcome) : OracleCovered rowCases667 p outcome := by
  cases h322 : p 322 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_west, advanceAt318_west, advanceAt319_west, advanceAt320_west, advanceAt321_east, advanceAt321_west, advanceAt322_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_west, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_west, advanceAt318_west, advanceAt319_west, advanceAt320_west, advanceAt321_east, advanceAt321_west, advanceAt322_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_west, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover668 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .northEast = some outcome) : OracleCovered rowCases668 p outcome := by
  cases h322 : p 322 with
  | false =>
    cases h296 : p 296 with
    | false =>
      cases h297 : p 297 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .northEast = some (.walk 297) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_north, advanceAt322_east, advanceAt322_northEast, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, cornerAt322_northEast, h296, h297, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case617.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case617, memberCase617, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame617.bindings p
        intro binding member
        simp only [frame617, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h296
        · exact h297
        · exact h322
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_north, advanceAt322_east, advanceAt322_northEast, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, cornerAt322_northEast, h296, h297, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_north, advanceAt322_east, advanceAt322_northEast, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, cornerAt322_northEast, h296, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_north, advanceAt322_east, advanceAt322_northEast, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, cornerAt322_northEast, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover669 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .northWest = some outcome) : OracleCovered rowCases669 p outcome := by
  cases h322 : p 322 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_north, advanceAt322_west, advanceAt322_northWest, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_northWest, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_north, advanceAt322_west, advanceAt322_northWest, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_northWest, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover670 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .southEast = some outcome) : OracleCovered rowCases670 p outcome := by
  cases h322 : p 322 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_south, advanceAt322_east, advanceAt322_southEast, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, cornerAt322_southEast, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_south, advanceAt322_east, advanceAt322_southEast, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, cornerAt322_southEast, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover671 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .southWest = some outcome) : OracleCovered rowCases671 p outcome := by
  cases h322 : p 322 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_south, advanceAt322_west, advanceAt322_southWest, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt322_southWest, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 322 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_south, advanceAt322_west, advanceAt322_southWest, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt322_southWest, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P02
