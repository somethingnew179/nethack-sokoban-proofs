import NetHack.Soko12Forward220.Unified.P00.OracleCover27
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover336 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .north = some outcome) : OracleCovered rowCases336 p outcome := by
  cases h210 : p 210 with
  | false =>
    cases h184 : p 184 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .north = some (.walk 184) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt132_north, advanceAt158_north, advanceAt184_north, advanceAt184_south, advanceAt210_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, cornerAt210_north, h184, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case305.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case305, memberCase305, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame305.bindings p
      intro binding member
      simp only [frame305, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h184
      · exact h210
    | true =>
      cases h158 : p 158 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .north = some (.push 184 (.stay 158)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt132_north, advanceAt158_north, advanceAt184_north, advanceAt184_south, advanceAt210_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, cornerAt210_north, h158, h184, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case720.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case720, memberCase720, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame720.bindings p
        intro binding member
        simp only [frame720, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h158
        · exact h184
        · exact h210
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt132_north, advanceAt158_north, advanceAt184_north, advanceAt184_south, advanceAt210_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, cornerAt210_north, h158, h184, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt132_north, advanceAt158_north, advanceAt184_north, advanceAt184_south, advanceAt210_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, cornerAt210_north, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover337 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .south = some outcome) : OracleCovered rowCases337 p outcome := by
  cases h210 : p 210 with
  | false =>
    cases h236 : p 236 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .south = some (.walk 236) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_south, advanceAt236_north, advanceAt236_south, advanceAt262_south, advanceAt288_south, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt210_south, h210, h236, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case306.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case306, memberCase306, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame306.bindings p
      intro binding member
      simp only [frame306, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h210
      · exact h236
    | true =>
      cases h262 : p 262 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .south = some (.push 236 (.stay 262)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_south, advanceAt236_north, advanceAt236_south, advanceAt262_south, advanceAt288_south, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt210_south, h210, h236, h262, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case781.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case781, memberCase781, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame781.bindings p
        intro binding member
        simp only [frame781, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h210
        · exact h236
        · exact h262
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_south, advanceAt236_north, advanceAt236_south, advanceAt262_south, advanceAt288_south, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt210_south, h210, h236, h262, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_south, advanceAt236_north, advanceAt236_south, advanceAt262_south, advanceAt288_south, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt210_south, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover338 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .east = some outcome) : OracleCovered rowCases338 p outcome := by
  cases h210 : p 210 with
  | false =>
    cases h211 : p 211 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .east = some (.walk 211) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_east, advanceAt211_east, advanceAt211_west, advanceAt212_east, advanceAt213_east, advanceAt214_east, advanceAt215_east, advanceAt216_east, advanceAt217_east, advanceAt218_east, advanceAt219_east, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt210_east, h210, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case307.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case307, memberCase307, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame307.bindings p
      intro binding member
      simp only [frame307, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h210
      · exact h211
    | true =>
      cases h212 : p 212 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .east = some (.push 211 (.stay 212)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_east, advanceAt211_east, advanceAt211_west, advanceAt212_east, advanceAt213_east, advanceAt214_east, advanceAt215_east, advanceAt216_east, advanceAt217_east, advanceAt218_east, advanceAt219_east, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt210_east, h210, h211, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case754.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case754, memberCase754, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame754.bindings p
        intro binding member
        simp only [frame754, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h210
        · exact h211
        · exact h212
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_east, advanceAt211_east, advanceAt211_west, advanceAt212_east, advanceAt213_east, advanceAt214_east, advanceAt215_east, advanceAt216_east, advanceAt217_east, advanceAt218_east, advanceAt219_east, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt210_east, h210, h211, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_east, advanceAt211_east, advanceAt211_west, advanceAt212_east, advanceAt213_east, advanceAt214_east, advanceAt215_east, advanceAt216_east, advanceAt217_east, advanceAt218_east, advanceAt219_east, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt210_east, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover339 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .west = some outcome) : OracleCovered rowCases339 p outcome := by
  cases h210 : p 210 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_east, advanceAt209_west, advanceAt210_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, cornerAt210_west, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_east, advanceAt209_west, advanceAt210_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, cornerAt210_west, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover340 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .northEast = some outcome) : OracleCovered rowCases340 p outcome := by
  cases h210 : p 210 with
  | false =>
    cases h184 : p 184 with
    | false =>
      cases h185 : p 185 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .northEast = some (.walk 185) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_north, advanceAt210_east, advanceAt210_northEast, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt210_northEast, h184, h185, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case308.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case308, memberCase308, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame308.bindings p
        intro binding member
        simp only [frame308, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h184
        · exact h185
        · exact h210
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_north, advanceAt210_east, advanceAt210_northEast, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt210_northEast, h184, h185, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h211 : p 211 with
      | false =>
        cases h185 : p 185 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .northEast = some (.walk 185) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_north, advanceAt210_east, advanceAt210_northEast, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt210_northEast, h184, h185, h210, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case309.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case309, memberCase309, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame309.bindings p
          intro binding member
          simp only [frame309, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h185
          · exact h210
          · exact h211
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_north, advanceAt210_east, advanceAt210_northEast, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt210_northEast, h184, h185, h210, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_north, advanceAt210_east, advanceAt210_northEast, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt210_northEast, h184, h210, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_north, advanceAt210_east, advanceAt210_northEast, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt210_northEast, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover341 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .northWest = some outcome) : OracleCovered rowCases341 p outcome := by
  cases h210 : p 210 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_north, advanceAt210_west, advanceAt210_northWest, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, cornerAt210_northWest, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_north, advanceAt210_west, advanceAt210_northWest, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, cornerAt210_northWest, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover342 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .southEast = some outcome) : OracleCovered rowCases342 p outcome := by
  cases h210 : p 210 with
  | false =>
    cases h236 : p 236 with
    | false =>
      cases h237 : p 237 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .southEast = some (.walk 237) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_south, advanceAt210_east, advanceAt210_southEast, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, cornerAt210_southEast, h210, h236, h237, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case310.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case310, memberCase310, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame310.bindings p
        intro binding member
        simp only [frame310, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h210
        · exact h236
        · exact h237
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_south, advanceAt210_east, advanceAt210_southEast, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, cornerAt210_southEast, h210, h236, h237, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h211 : p 211 with
      | false =>
        cases h237 : p 237 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .southEast = some (.walk 237) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_south, advanceAt210_east, advanceAt210_southEast, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, cornerAt210_southEast, h210, h211, h236, h237, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case311.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case311, memberCase311, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame311.bindings p
          intro binding member
          simp only [frame311, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h210
          · exact h211
          · exact h237
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_south, advanceAt210_east, advanceAt210_southEast, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, cornerAt210_southEast, h210, h211, h236, h237, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_south, advanceAt210_east, advanceAt210_southEast, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, cornerAt210_southEast, h210, h211, h236, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_south, advanceAt210_east, advanceAt210_southEast, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, cornerAt210_southEast, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover343 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .southWest = some outcome) : OracleCovered rowCases343 p outcome := by
  cases h210 : p 210 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_south, advanceAt210_west, advanceAt210_southWest, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, cornerAt210_southWest, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 210 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt210_south, advanceAt210_west, advanceAt210_southWest, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, cornerAt210_southWest, h210, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover344 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .north = some outcome) : OracleCovered rowCases344 p outcome := by
  cases h211 : p 211 with
  | false =>
    cases h185 : p 185 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .north = some (.walk 185) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt55_north, advanceAt81_north, advanceAt107_north, advanceAt133_north, advanceAt159_north, advanceAt185_north, advanceAt185_south, advanceAt211_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt211_north, h185, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case312.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case312, memberCase312, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame312.bindings p
      intro binding member
      simp only [frame312, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h185
      · exact h211
    | true =>
      cases h159 : p 159 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .north = some (.push 185 (.stay 159)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt55_north, advanceAt81_north, advanceAt107_north, advanceAt133_north, advanceAt159_north, advanceAt185_north, advanceAt185_south, advanceAt211_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt211_north, h159, h185, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case722.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case722, memberCase722, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame722.bindings p
        intro binding member
        simp only [frame722, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h159
        · exact h185
        · exact h211
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt55_north, advanceAt81_north, advanceAt107_north, advanceAt133_north, advanceAt159_north, advanceAt185_north, advanceAt185_south, advanceAt211_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt211_north, h159, h185, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt55_north, advanceAt81_north, advanceAt107_north, advanceAt133_north, advanceAt159_north, advanceAt185_north, advanceAt185_south, advanceAt211_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt211_north, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover345 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .south = some outcome) : OracleCovered rowCases345 p outcome := by
  cases h211 : p 211 with
  | false =>
    cases h237 : p 237 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .south = some (.walk 237) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt211_south, advanceAt237_north, advanceAt237_south, advanceAt263_south, advanceAt289_south, advanceAt315_south, advanceAt341_south, advanceAt367_south, advanceAt393_south, advanceAt419_south, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt419, doorAt419, trapAt419, boxAt419, holeAt419, cornerAt211_south, h211, h237, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case313.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case313, memberCase313, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame313.bindings p
      intro binding member
      simp only [frame313, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h211
      · exact h237
    | true =>
      cases h263 : p 263 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .south = some (.push 237 (.stay 263)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt211_south, advanceAt237_north, advanceAt237_south, advanceAt263_south, advanceAt289_south, advanceAt315_south, advanceAt341_south, advanceAt367_south, advanceAt393_south, advanceAt419_south, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt419, doorAt419, trapAt419, boxAt419, holeAt419, cornerAt211_south, h211, h237, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case783.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case783, memberCase783, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame783.bindings p
        intro binding member
        simp only [frame783, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h211
        · exact h237
        · exact h263
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt211_south, advanceAt237_north, advanceAt237_south, advanceAt263_south, advanceAt289_south, advanceAt315_south, advanceAt341_south, advanceAt367_south, advanceAt393_south, advanceAt419_south, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt419, doorAt419, trapAt419, boxAt419, holeAt419, cornerAt211_south, h211, h237, h263, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt211_south, advanceAt237_north, advanceAt237_south, advanceAt263_south, advanceAt289_south, advanceAt315_south, advanceAt341_south, advanceAt367_south, advanceAt393_south, advanceAt419_south, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt419, doorAt419, trapAt419, boxAt419, holeAt419, cornerAt211_south, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover346 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .east = some outcome) : OracleCovered rowCases346 p outcome := by
  cases h211 : p 211 with
  | false =>
    cases h212 : p 212 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .east = some (.walk 212) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt211_east, advanceAt212_east, advanceAt212_west, advanceAt213_east, advanceAt214_east, advanceAt215_east, advanceAt216_east, advanceAt217_east, advanceAt218_east, advanceAt219_east, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt211_east, h211, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case314.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case314, memberCase314, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame314.bindings p
      intro binding member
      simp only [frame314, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h211
      · exact h212
    | true =>
      cases h213 : p 213 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .east = some (.push 212 (.stay 213)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt211_east, advanceAt212_east, advanceAt212_west, advanceAt213_east, advanceAt214_east, advanceAt215_east, advanceAt216_east, advanceAt217_east, advanceAt218_east, advanceAt219_east, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt211_east, h211, h212, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case758.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case758, memberCase758, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame758.bindings p
        intro binding member
        simp only [frame758, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h211
        · exact h212
        · exact h213
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt211_east, advanceAt212_east, advanceAt212_west, advanceAt213_east, advanceAt214_east, advanceAt215_east, advanceAt216_east, advanceAt217_east, advanceAt218_east, advanceAt219_east, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt211_east, h211, h212, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt211_east, advanceAt212_east, advanceAt212_west, advanceAt213_east, advanceAt214_east, advanceAt215_east, advanceAt216_east, advanceAt217_east, advanceAt218_east, advanceAt219_east, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt211_east, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover347 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .west = some outcome) : OracleCovered rowCases347 p outcome := by
  cases h211 : p 211 with
  | false =>
    cases h210 : p 210 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .west = some (.walk 210) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_east, advanceAt210_west, advanceAt211_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt211_west, h210, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case315.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case315, memberCase315, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame315.bindings p
      intro binding member
      simp only [frame315, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h210
      · exact h211
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_east, advanceAt210_west, advanceAt211_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt211_west, h210, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 211 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_east, advanceAt210_west, advanceAt211_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, cornerAt211_west, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P00
