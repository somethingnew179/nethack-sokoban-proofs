import NetHack.Soko12Forward220.Unified.P05.OracleCover02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover36 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 33 .northEast = some outcome) : OracleCovered rowCases36 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 33 .northEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt33_north, advanceAt33_east, advanceAt33_northEast, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, cornerAt33_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover37 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 33 .northWest = some outcome) : OracleCovered rowCases37 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 33 .northWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt33_north, advanceAt33_west, advanceAt33_northWest, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, cornerAt33_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover38 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 33 .southEast = some outcome) : OracleCovered rowCases38 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 33 .southEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt33_south, advanceAt33_east, advanceAt33_southEast, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, cornerAt33_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover39 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 33 .southWest = some outcome) : OracleCovered rowCases39 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 33 .southWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt33_south, advanceAt33_west, advanceAt33_southWest, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, cornerAt33_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover40 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .north = some outcome) : OracleCovered rowCases40 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .north = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt8_south, advanceAt34_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, cornerAt34_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover41 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .south = some outcome) : OracleCovered rowCases41 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .south = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt34_south, advanceAt60_north, advanceAt60_south, advanceAt86_south, advanceAt112_south, advanceAt138_south, advanceAt164_south, advanceAt190_south, advanceAt216_south, advanceAt242_south, advanceAt268_south, advanceAt294_south, advanceAt320_south, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt34_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover42 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .east = some outcome) : OracleCovered rowCases42 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .east = some (.walk 35) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt34_east, advanceAt35_east, advanceAt35_west, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, advanceAt44_east, advanceAt45_east, advanceAt46_east, advanceAt47_east, advanceAt48_east, advanceAt49_east, advanceAt50_east, advanceAt51_east, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt34_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = case015.outcome := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨case015, memberCase015, same, ?_⟩
  change DecisionDAGTransform.Satisfies frame015.bindings p
  intro binding member
  cases member
theorem oracleCover43 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .west = some outcome) : OracleCovered rowCases43 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .west = some (.walk 33) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_west, advanceAt30_west, advanceAt31_west, advanceAt32_west, advanceAt33_east, advanceAt33_west, advanceAt34_west, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, cornerAt34_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = case016.outcome := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨case016, memberCase016, same, ?_⟩
  change DecisionDAGTransform.Satisfies frame016.bindings p
  intro binding member
  cases member
theorem oracleCover44 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .northEast = some outcome) : OracleCovered rowCases44 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .northEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt34_north, advanceAt34_east, advanceAt34_northEast, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, cornerAt34_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover45 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .northWest = some outcome) : OracleCovered rowCases45 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .northWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt34_north, advanceAt34_west, advanceAt34_northWest, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, cornerAt34_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover46 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .southEast = some outcome) : OracleCovered rowCases46 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .southEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt34_south, advanceAt34_east, advanceAt34_southEast, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, cornerAt34_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover47 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .southWest = some outcome) : OracleCovered rowCases47 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 34 .southWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt34_south, advanceAt34_west, advanceAt34_southWest, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, cornerAt34_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
end NetHack.Soko12Forward220.Unified.P05
