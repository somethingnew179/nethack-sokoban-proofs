import NetHack.Soko12Forward220.Unified.P05.OracleCover04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover60 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 36 .northEast = some outcome) : OracleCovered rowCases60 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 36 .northEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt36_north, advanceAt36_east, advanceAt36_northEast, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, cornerAt36_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover61 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 36 .northWest = some outcome) : OracleCovered rowCases61 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 36 .northWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt36_north, advanceAt36_west, advanceAt36_northWest, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, cornerAt36_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover62 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 36 .southEast = some outcome) : OracleCovered rowCases62 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 36 .southEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt36_south, advanceAt36_east, advanceAt36_southEast, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, cornerAt36_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover63 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 36 .southWest = some outcome) : OracleCovered rowCases63 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 36 .southWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt36_south, advanceAt36_west, advanceAt36_southWest, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, cornerAt36_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover64 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .north = some outcome) : OracleCovered rowCases64 p outcome := by
  cases h29 : p 29 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .north = some (.walk 29) := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt29_south, advanceAt55_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, cornerAt55_north, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case020.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case020, memberCase020, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame020.bindings p
    intro binding member
    simp only [frame020, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h29
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt29_south, advanceAt55_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, cornerAt55_north, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover65 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .south = some outcome) : OracleCovered rowCases65 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .south = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_south, advanceAt81_north, advanceAt81_south, advanceAt107_south, advanceAt133_south, advanceAt159_south, advanceAt185_south, advanceAt211_south, advanceAt237_south, advanceAt263_south, advanceAt289_south, advanceAt315_south, advanceAt341_south, advanceAt367_south, advanceAt393_south, advanceAt419_south, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt419, doorAt419, trapAt419, boxAt419, holeAt419, cornerAt55_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover66 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .east = some outcome) : OracleCovered rowCases66 p outcome := by
  cases h56 : p 56 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .east = some (.walk 56) := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_east, advanceAt56_east, advanceAt56_west, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, advanceAt66_east, advanceAt67_east, advanceAt68_east, advanceAt69_east, advanceAt70_east, advanceAt71_east, advanceAt72_east, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, cornerAt55_east, h56, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case021.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case021, memberCase021, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame021.bindings p
    intro binding member
    simp only [frame021, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h56
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_east, advanceAt56_east, advanceAt56_west, advanceAt57_east, advanceAt58_east, advanceAt59_east, advanceAt60_east, advanceAt61_east, advanceAt62_east, advanceAt63_east, advanceAt64_east, advanceAt65_east, advanceAt66_east, advanceAt67_east, advanceAt68_east, advanceAt69_east, advanceAt70_east, advanceAt71_east, advanceAt72_east, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt64, doorAt64, trapAt64, boxAt64, holeAt64, floorAt65, doorAt65, trapAt65, boxAt65, holeAt65, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, cornerAt55_east, h56, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover67 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .west = some outcome) : OracleCovered rowCases67 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .west = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt52_west, advanceAt53_west, advanceAt54_east, advanceAt54_west, advanceAt55_west, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, cornerAt55_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover68 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .northEast = some outcome) : OracleCovered rowCases68 p outcome := by
  cases h29 : p 29 with
  | false =>
    cases h30 : p 30 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .northEast = some (.walk 30) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_north, advanceAt55_east, advanceAt55_northEast, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, cornerAt55_northEast, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, clearAt30_37, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case022.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case022, memberCase022, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame022.bindings p
      intro binding member
      simp only [frame022, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h29
      · exact h30
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_north, advanceAt55_east, advanceAt55_northEast, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, cornerAt55_northEast, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, clearAt30_37, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    cases h56 : p 56 with
    | false =>
      cases h30 : p 30 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .northEast = some (.walk 30) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_north, advanceAt55_east, advanceAt55_northEast, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, cornerAt55_northEast, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, clearAt30_37, h29, h30, h56, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case023.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case023, memberCase023, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame023.bindings p
        intro binding member
        simp only [frame023, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact h30
        · exact h56
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_north, advanceAt55_east, advanceAt55_northEast, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, cornerAt55_northEast, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, clearAt30_37, h29, h30, h56, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_north, advanceAt55_east, advanceAt55_northEast, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, cornerAt55_northEast, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, clearAt30_37, h29, h56, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
theorem oracleCover69 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .northWest = some outcome) : OracleCovered rowCases69 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .northWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_north, advanceAt55_west, advanceAt55_northWest, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, cornerAt55_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover70 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .southEast = some outcome) : OracleCovered rowCases70 p outcome := by
  cases h56 : p 56 with
  | false =>
    cases h82 : p 82 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .southEast = some (.walk 82) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_south, advanceAt55_east, advanceAt55_southEast, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, cornerAt55_southEast, h56, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case024.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case024, memberCase024, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame024.bindings p
      intro binding member
      simp only [frame024, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h56
      · exact h82
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_south, advanceAt55_east, advanceAt55_southEast, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, cornerAt55_southEast, h56, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_south, advanceAt55_east, advanceAt55_southEast, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, cornerAt55_southEast, h56, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover71 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .southWest = some outcome) : OracleCovered rowCases71 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 55 .southWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt55_south, advanceAt55_west, advanceAt55_southWest, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, cornerAt55_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
end NetHack.Soko12Forward220.Unified.P05
