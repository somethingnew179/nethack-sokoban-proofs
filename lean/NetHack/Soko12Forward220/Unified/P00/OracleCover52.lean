import NetHack.Soko12Forward220.Unified.P00.OracleCover51
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover624 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .north = some outcome) : OracleCovered rowCases624 p outcome := by
  cases h318 : p 318 with
  | false =>
    cases h292 : p 292 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .north = some (.walk 292) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt214_north, advanceAt240_north, advanceAt266_north, advanceAt292_north, advanceAt292_south, advanceAt318_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt318_north, h292, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case590.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case590, memberCase590, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame590.bindings p
      intro binding member
      simp only [frame590, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h292
      · exact h318
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt214_north, advanceAt240_north, advanceAt266_north, advanceAt292_north, advanceAt292_south, advanceAt318_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt318_north, h292, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt214_north, advanceAt240_north, advanceAt266_north, advanceAt292_north, advanceAt292_south, advanceAt318_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt318_north, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover625 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .south = some outcome) : OracleCovered rowCases625 p outcome := by
  cases h318 : p 318 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_south, advanceAt344_north, advanceAt344_south, advanceAt370_south, advanceAt396_south, advanceAt422_south, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, cornerAt318_south, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_south, advanceAt344_north, advanceAt344_south, advanceAt370_south, advanceAt396_south, advanceAt422_south, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, cornerAt318_south, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover626 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .east = some outcome) : OracleCovered rowCases626 p outcome := by
  cases h318 : p 318 with
  | false =>
    cases h319 : p 319 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .east = some (.walk 319) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_east, advanceAt319_east, advanceAt319_west, advanceAt320_east, advanceAt321_east, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt318_east, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case591.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case591, memberCase591, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame591.bindings p
      intro binding member
      simp only [frame591, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h318
      · exact h319
    | true =>
      cases h320 : p 320 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .east = some (.push 319 (.stay 320)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_east, advanceAt319_east, advanceAt319_west, advanceAt320_east, advanceAt321_east, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt318_east, h318, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case836.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case836, memberCase836, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame836.bindings p
        intro binding member
        simp only [frame836, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h318
        · exact h319
        · exact h320
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_east, advanceAt319_east, advanceAt319_west, advanceAt320_east, advanceAt321_east, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt318_east, h318, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_east, advanceAt319_east, advanceAt319_west, advanceAt320_east, advanceAt321_east, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt318_east, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover627 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .west = some outcome) : OracleCovered rowCases627 p outcome := by
  cases h318 : p 318 with
  | false =>
    cases h317 : p 317 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .west = some (.walk 317) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_east, advanceAt317_west, advanceAt318_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt318_west, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case592.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case592, memberCase592, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame592.bindings p
      intro binding member
      simp only [frame592, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h317
      · exact h318
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_east, advanceAt317_west, advanceAt318_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt318_west, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_east, advanceAt317_west, advanceAt318_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt318_west, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover628 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northEast = some outcome) : OracleCovered rowCases628 p outcome := by
  cases h318 : p 318 with
  | false =>
    cases h292 : p 292 with
    | false =>
      cases h293 : p 293 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northEast = some (.walk 293) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_north, advanceAt318_east, advanceAt318_northEast, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt318_northEast, h292, h293, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case593.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case593, memberCase593, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame593.bindings p
        intro binding member
        simp only [frame593, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h292
        · exact h293
        · exact h318
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_north, advanceAt318_east, advanceAt318_northEast, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt318_northEast, h292, h293, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h319 : p 319 with
      | false =>
        cases h293 : p 293 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northEast = some (.walk 293) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_north, advanceAt318_east, advanceAt318_northEast, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt318_northEast, h292, h293, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case594.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case594, memberCase594, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame594.bindings p
          intro binding member
          simp only [frame594, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h293
          · exact h318
          · exact h319
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_north, advanceAt318_east, advanceAt318_northEast, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt318_northEast, h292, h293, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_north, advanceAt318_east, advanceAt318_northEast, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt318_northEast, h292, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_north, advanceAt318_east, advanceAt318_northEast, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt318_northEast, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover629 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northWest = some outcome) : OracleCovered rowCases629 p outcome := by
  cases h318 : p 318 with
  | false =>
    cases h292 : p 292 with
    | false =>
      cases h291 : p 291 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northWest = some (.walk 291) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_north, advanceAt318_west, advanceAt318_northWest, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt318_northWest, h291, h292, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case595.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case595, memberCase595, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame595.bindings p
        intro binding member
        simp only [frame595, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h291
        · exact h292
        · exact h318
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_north, advanceAt318_west, advanceAt318_northWest, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt318_northWest, h291, h292, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h317 : p 317 with
      | false =>
        cases h291 : p 291 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northWest = some (.walk 291) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_north, advanceAt318_west, advanceAt318_northWest, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt318_northWest, h291, h292, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case596.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case596, memberCase596, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame596.bindings p
          intro binding member
          simp only [frame596, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h291
          · exact h317
          · exact h318
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_north, advanceAt318_west, advanceAt318_northWest, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt318_northWest, h291, h292, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_north, advanceAt318_west, advanceAt318_northWest, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt318_northWest, h292, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_north, advanceAt318_west, advanceAt318_northWest, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt318_northWest, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover630 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .southEast = some outcome) : OracleCovered rowCases630 p outcome := by
  cases h318 : p 318 with
  | false =>
    cases h319 : p 319 with
    | false =>
      cases h345 : p 345 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .southEast = some (.walk 345) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_south, advanceAt318_east, advanceAt318_southEast, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt318_southEast, h318, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case597.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case597, memberCase597, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame597.bindings p
        intro binding member
        simp only [frame597, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h318
        · exact h319
        · exact h345
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_south, advanceAt318_east, advanceAt318_southEast, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt318_southEast, h318, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_south, advanceAt318_east, advanceAt318_southEast, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt318_southEast, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_south, advanceAt318_east, advanceAt318_southEast, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt318_southEast, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover631 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .southWest = some outcome) : OracleCovered rowCases631 p outcome := by
  cases h318 : p 318 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_south, advanceAt318_west, advanceAt318_southWest, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, cornerAt318_southWest, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 318 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt318_south, advanceAt318_west, advanceAt318_southWest, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, cornerAt318_southWest, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover632 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .north = some outcome) : OracleCovered rowCases632 p outcome := by
  cases h319 : p 319 with
  | false =>
    cases h293 : p 293 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .north = some (.walk 293) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt293_south, advanceAt319_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt319_north, h293, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case598.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case598, memberCase598, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame598.bindings p
      intro binding member
      simp only [frame598, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h293
      · exact h319
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt293_south, advanceAt319_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt319_north, h293, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt293_south, advanceAt319_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt319_north, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover633 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .south = some outcome) : OracleCovered rowCases633 p outcome := by
  cases h319 : p 319 with
  | false =>
    cases h345 : p 345 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .south = some (.walk 345) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt319_south, advanceAt345_north, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt319_south, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case599.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case599, memberCase599, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame599.bindings p
      intro binding member
      simp only [frame599, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h319
      · exact h345
    | true =>
      cases h371 : p 371 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .south = some (.push 345 (.stay 371)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt319_south, advanceAt345_north, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt319_south, h319, h345, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case841.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case841, memberCase841, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame841.bindings p
        intro binding member
        simp only [frame841, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h319
        · exact h345
        · exact h371
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt319_south, advanceAt345_north, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt319_south, h319, h345, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt319_south, advanceAt345_north, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt319_south, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover634 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .east = some outcome) : OracleCovered rowCases634 p outcome := by
  cases h319 : p 319 with
  | false =>
    cases h320 : p 320 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .east = some (.walk 320) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt319_east, advanceAt320_east, advanceAt320_west, advanceAt321_east, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt319_east, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case600.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case600, memberCase600, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame600.bindings p
      intro binding member
      simp only [frame600, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h319
      · exact h320
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt319_east, advanceAt320_east, advanceAt320_west, advanceAt321_east, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt319_east, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt319_east, advanceAt320_east, advanceAt320_west, advanceAt321_east, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt319_east, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover635 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .west = some outcome) : OracleCovered rowCases635 p outcome := by
  cases h319 : p 319 with
  | false =>
    cases h318 : p 318 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .west = some (.walk 318) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_west, advanceAt318_east, advanceAt318_west, advanceAt319_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt319_west, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case601.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case601, memberCase601, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame601.bindings p
      intro binding member
      simp only [frame601, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h318
      · exact h319
    | true =>
      cases h317 : p 317 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .west = some (.push 318 (.stay 317)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_west, advanceAt318_east, advanceAt318_west, advanceAt319_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt319_west, h317, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case833.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case833, memberCase833, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame833.bindings p
        intro binding member
        simp only [frame833, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h317
        · exact h318
        · exact h319
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_west, advanceAt318_east, advanceAt318_west, advanceAt319_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt319_west, h317, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 319 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_west, advanceAt318_east, advanceAt318_west, advanceAt319_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, cornerAt319_west, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P00
