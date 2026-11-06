import NetHack.Soko12Forward220.Unified.P05.OracleCover41
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover504 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .north = some outcome) : OracleCovered rowCases504 p outcome := by
  cases h244 : p 244 with
  | false =>
    cases h218 : p 218 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .north = some (.walk 218) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt218_south, advanceAt244_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, cornerAt244_north, h218, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case451.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case451, memberCase451, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame451.bindings p
      intro binding member
      simp only [frame451, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h218
      · exact h244
    | true =>
      cases h192 : p 192 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .north = some (.push 218 (.stay 192)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt218_south, advanceAt244_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, cornerAt244_north, h192, h218, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case782.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case782, memberCase782, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame782.bindings p
        intro binding member
        simp only [frame782, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h192
        · exact h218
        · exact h244
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt218_south, advanceAt244_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, cornerAt244_north, h192, h218, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt218_south, advanceAt244_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, cornerAt244_north, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover505 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .south = some outcome) : OracleCovered rowCases505 p outcome := by
  cases h244 : p 244 with
  | false =>
    cases h270 : p 270 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .south = some (.walk 270) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_south, advanceAt270_north, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt244_south, h244, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case452.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case452, memberCase452, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame452.bindings p
      intro binding member
      simp only [frame452, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h244
      · exact h270
    | true =>
      cases h296 : p 296 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .south = some (.push 270 (.stay 296)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_south, advanceAt270_north, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt244_south, h244, h270, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case823.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case823, memberCase823, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame823.bindings p
        intro binding member
        simp only [frame823, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h244
        · exact h270
        · exact h296
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_south, advanceAt270_north, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt244_south, h244, h270, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_south, advanceAt270_north, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt244_south, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover506 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .east = some outcome) : OracleCovered rowCases506 p outcome := by
  cases h244 : p 244 with
  | false =>
    cases h245 : p 245 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .east = some (.walk 245) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_east, advanceAt245_east, advanceAt245_west, advanceAt246_east, advanceAt247_east, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, cornerAt244_east, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case453.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case453, memberCase453, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame453.bindings p
      intro binding member
      simp only [frame453, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h244
      · exact h245
    | true =>
      cases h246 : p 246 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .east = some (.push 245 (.stay 246)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_east, advanceAt245_east, advanceAt245_west, advanceAt246_east, advanceAt247_east, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, cornerAt244_east, h244, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case806.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case806, memberCase806, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame806.bindings p
        intro binding member
        simp only [frame806, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h244
        · exact h245
        · exact h246
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_east, advanceAt245_east, advanceAt245_west, advanceAt246_east, advanceAt247_east, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, cornerAt244_east, h244, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_east, advanceAt245_east, advanceAt245_west, advanceAt246_east, advanceAt247_east, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, cornerAt244_east, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover507 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .west = some outcome) : OracleCovered rowCases507 p outcome := by
  cases h244 : p 244 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt234_west, advanceAt235_west, advanceAt236_west, advanceAt237_west, advanceAt238_west, advanceAt239_west, advanceAt240_west, advanceAt241_west, advanceAt242_west, advanceAt243_east, advanceAt243_west, advanceAt244_west, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, cornerAt244_west, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt234_west, advanceAt235_west, advanceAt236_west, advanceAt237_west, advanceAt238_west, advanceAt239_west, advanceAt240_west, advanceAt241_west, advanceAt242_west, advanceAt243_east, advanceAt243_west, advanceAt244_west, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, cornerAt244_west, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover508 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .northEast = some outcome) : OracleCovered rowCases508 p outcome := by
  cases h244 : p 244 with
  | false =>
    cases h218 : p 218 with
    | false =>
      cases h219 : p 219 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .northEast = some (.walk 219) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_north, advanceAt244_east, advanceAt244_northEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt244_northEast, h218, h219, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case454.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case454, memberCase454, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame454.bindings p
        intro binding member
        simp only [frame454, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h218
        · exact h219
        · exact h244
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_north, advanceAt244_east, advanceAt244_northEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt244_northEast, h218, h219, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h245 : p 245 with
      | false =>
        cases h219 : p 219 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .northEast = some (.walk 219) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_north, advanceAt244_east, advanceAt244_northEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt244_northEast, h218, h219, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case455.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case455, memberCase455, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame455.bindings p
          intro binding member
          simp only [frame455, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h219
          · exact h244
          · exact h245
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_north, advanceAt244_east, advanceAt244_northEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt244_northEast, h218, h219, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_north, advanceAt244_east, advanceAt244_northEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt244_northEast, h218, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_north, advanceAt244_east, advanceAt244_northEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt244_northEast, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover509 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .northWest = some outcome) : OracleCovered rowCases509 p outcome := by
  cases h244 : p 244 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_north, advanceAt244_west, advanceAt244_northWest, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, cornerAt244_northWest, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_north, advanceAt244_west, advanceAt244_northWest, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, cornerAt244_northWest, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover510 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .southEast = some outcome) : OracleCovered rowCases510 p outcome := by
  cases h244 : p 244 with
  | false =>
    cases h270 : p 270 with
    | false =>
      cases h271 : p 271 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .southEast = some (.walk 271) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_south, advanceAt244_east, advanceAt244_southEast, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt244_southEast, h244, h270, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case456.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case456, memberCase456, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame456.bindings p
        intro binding member
        simp only [frame456, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h244
        · exact h270
        · exact h271
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_south, advanceAt244_east, advanceAt244_southEast, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt244_southEast, h244, h270, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h245 : p 245 with
      | false =>
        cases h271 : p 271 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .southEast = some (.walk 271) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_south, advanceAt244_east, advanceAt244_southEast, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt244_southEast, h244, h245, h270, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case457.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case457, memberCase457, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame457.bindings p
          intro binding member
          simp only [frame457, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h244
          · exact h245
          · exact h271
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_south, advanceAt244_east, advanceAt244_southEast, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt244_southEast, h244, h245, h270, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_south, advanceAt244_east, advanceAt244_southEast, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt244_southEast, h244, h245, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_south, advanceAt244_east, advanceAt244_southEast, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt244_southEast, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover511 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .southWest = some outcome) : OracleCovered rowCases511 p outcome := by
  cases h244 : p 244 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_south, advanceAt244_west, advanceAt244_southWest, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt244_southWest, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 244 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt244_south, advanceAt244_west, advanceAt244_southWest, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt244_southWest, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover512 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .north = some outcome) : OracleCovered rowCases512 p outcome := by
  cases h245 : p 245 with
  | false =>
    cases h219 : p 219 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .north = some (.walk 219) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt167_north, advanceAt193_north, advanceAt219_north, advanceAt219_south, advanceAt245_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt245_north, h219, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case458.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case458, memberCase458, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame458.bindings p
      intro binding member
      simp only [frame458, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h219
      · exact h245
    | true =>
      cases h193 : p 193 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .north = some (.push 219 (.stay 193)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt167_north, advanceAt193_north, advanceAt219_north, advanceAt219_south, advanceAt245_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt245_north, h193, h219, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case784.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case784, memberCase784, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame784.bindings p
        intro binding member
        simp only [frame784, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h193
        · exact h219
        · exact h245
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt167_north, advanceAt193_north, advanceAt219_north, advanceAt219_south, advanceAt245_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt245_north, h193, h219, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt167_north, advanceAt193_north, advanceAt219_north, advanceAt219_south, advanceAt245_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt245_north, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover513 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .south = some outcome) : OracleCovered rowCases513 p outcome := by
  cases h245 : p 245 with
  | false =>
    cases h271 : p 271 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .south = some (.walk 271) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_south, advanceAt271_north, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt245_south, h245, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case459.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case459, memberCase459, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame459.bindings p
      intro binding member
      simp only [frame459, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h245
      · exact h271
    | true =>
      cases h297 : p 297 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .south = some (.push 271 (.stay 297)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_south, advanceAt271_north, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt245_south, h245, h271, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case825.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case825, memberCase825, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame825.bindings p
        intro binding member
        simp only [frame825, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h245
        · exact h271
        · exact h297
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_south, advanceAt271_north, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt245_south, h245, h271, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_south, advanceAt271_north, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt245_south, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover514 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .east = some outcome) : OracleCovered rowCases514 p outcome := by
  cases h245 : p 245 with
  | false =>
    cases h246 : p 246 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .east = some (.walk 246) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_east, advanceAt246_east, advanceAt246_west, advanceAt247_east, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, cornerAt245_east, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case460.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case460, memberCase460, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame460.bindings p
      intro binding member
      simp only [frame460, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h245
      · exact h246
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_east, advanceAt246_east, advanceAt246_west, advanceAt247_east, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, cornerAt245_east, h245, h246, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt245_east, advanceAt246_east, advanceAt246_west, advanceAt247_east, advanceAt248_east, advanceAt249_east, advanceAt250_east, advanceAt251_east, advanceAt252_east, advanceAt253_east, advanceAt254_east, advanceAt255_east, advanceAt256_east, advanceAt257_east, advanceAt258_east, advanceAt259_east, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt251, doorAt251, trapAt251, boxAt251, holeAt251, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt253, doorAt253, trapAt253, boxAt253, holeAt253, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt256, doorAt256, trapAt256, boxAt256, holeAt256, floorAt257, doorAt257, trapAt257, boxAt257, holeAt257, floorAt258, doorAt258, trapAt258, boxAt258, holeAt258, floorAt259, doorAt259, trapAt259, boxAt259, holeAt259, cornerAt245_east, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover515 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .west = some outcome) : OracleCovered rowCases515 p outcome := by
  cases h245 : p 245 with
  | false =>
    cases h244 : p 244 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .west = some (.walk 244) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt234_west, advanceAt235_west, advanceAt236_west, advanceAt237_west, advanceAt238_west, advanceAt239_west, advanceAt240_west, advanceAt241_west, advanceAt242_west, advanceAt243_west, advanceAt244_east, advanceAt244_west, advanceAt245_west, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt245_west, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case461.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case461, memberCase461, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame461.bindings p
      intro binding member
      simp only [frame461, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h244
      · exact h245
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt234_west, advanceAt235_west, advanceAt236_west, advanceAt237_west, advanceAt238_west, advanceAt239_west, advanceAt240_west, advanceAt241_west, advanceAt242_west, advanceAt243_west, advanceAt244_east, advanceAt244_west, advanceAt245_west, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt245_west, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 245 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt234_west, advanceAt235_west, advanceAt236_west, advanceAt237_west, advanceAt238_west, advanceAt239_west, advanceAt240_west, advanceAt241_west, advanceAt242_west, advanceAt243_west, advanceAt244_east, advanceAt244_west, advanceAt245_west, floorAt234, doorAt234, trapAt234, boxAt234, holeAt234, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt245_west, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P05
