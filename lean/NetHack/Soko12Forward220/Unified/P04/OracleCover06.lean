import NetHack.Soko12Forward220.Unified.P04.OracleCover05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover72 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .north = some outcome) : OracleCovered rowCases72 p outcome := by
  cases h82 : p 82 with
  | false =>
    cases h56 : p 56 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .north = some (.walk 56) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt56_south, advanceAt82_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, cornerAt82_north, h56, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case028.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case028, memberCase028, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame028.bindings p
      intro binding member
      simp only [frame028, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h56
      · exact h82
    | true =>
      cases h30 : p 30 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .north = some (.push 56 (.stay 30)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt56_south, advanceAt82_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, cornerAt82_north, h30, h56, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case674.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case674, memberCase674, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame674.bindings p
        intro binding member
        simp only [frame674, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h30
        · exact h56
        · exact h82
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt56_south, advanceAt82_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, cornerAt82_north, h30, h56, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt56_south, advanceAt82_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, cornerAt82_north, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover73 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .south = some outcome) : OracleCovered rowCases73 p outcome := by
  cases h82 : p 82 with
  | false =>
    cases h108 : p 108 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .south = some (.walk 108) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_south, advanceAt108_north, advanceAt108_south, advanceAt134_south, advanceAt160_south, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt82_south, h82, h108, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case029.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case029, memberCase029, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame029.bindings p
      intro binding member
      simp only [frame029, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h82
      · exact h108
    | true =>
      cases h134 : p 134 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .south = some (.push 108 (.stay 134)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_south, advanceAt108_north, advanceAt108_south, advanceAt134_south, advanceAt160_south, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt82_south, h82, h108, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case679.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case679, memberCase679, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame679.bindings p
        intro binding member
        simp only [frame679, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h82
        · exact h108
        · exact h134
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_south, advanceAt108_north, advanceAt108_south, advanceAt134_south, advanceAt160_south, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt82_south, h82, h108, h134, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_south, advanceAt108_north, advanceAt108_south, advanceAt134_south, advanceAt160_south, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt82_south, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover74 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .east = some outcome) : OracleCovered rowCases74 p outcome := by
  cases h82 : p 82 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_east, advanceAt83_east, advanceAt83_west, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, advanceAt88_east, advanceAt89_east, advanceAt90_east, advanceAt91_east, advanceAt92_east, advanceAt93_east, advanceAt94_east, advanceAt95_east, advanceAt96_east, advanceAt97_east, advanceAt98_east, advanceAt99_east, advanceAt100_east, advanceAt101_east, advanceAt102_east, advanceAt103_east, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, cornerAt82_east, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_east, advanceAt83_east, advanceAt83_west, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, advanceAt88_east, advanceAt89_east, advanceAt90_east, advanceAt91_east, advanceAt92_east, advanceAt93_east, advanceAt94_east, advanceAt95_east, advanceAt96_east, advanceAt97_east, advanceAt98_east, advanceAt99_east, advanceAt100_east, advanceAt101_east, advanceAt102_east, advanceAt103_east, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, floorAt103, doorAt103, trapAt103, boxAt103, holeAt103, cornerAt82_east, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover75 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .west = some outcome) : OracleCovered rowCases75 p outcome := by
  cases h82 : p 82 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt78_west, advanceAt79_west, advanceAt80_west, advanceAt81_east, advanceAt81_west, advanceAt82_west, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, cornerAt82_west, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt78_west, advanceAt79_west, advanceAt80_west, advanceAt81_east, advanceAt81_west, advanceAt82_west, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, cornerAt82_west, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover76 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .northEast = some outcome) : OracleCovered rowCases76 p outcome := by
  cases h82 : p 82 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_north, advanceAt82_east, advanceAt82_northEast, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, cornerAt82_northEast, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_north, advanceAt82_east, advanceAt82_northEast, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, cornerAt82_northEast, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover77 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .northWest = some outcome) : OracleCovered rowCases77 p outcome := by
  cases h82 : p 82 with
  | false =>
    cases h56 : p 56 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .northWest = some (.walk 55) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_north, advanceAt82_west, advanceAt82_northWest, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, cornerAt82_northWest, h56, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case030.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case030, memberCase030, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame030.bindings p
      intro binding member
      simp only [frame030, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h56
      · exact h82
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_north, advanceAt82_west, advanceAt82_northWest, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, cornerAt82_northWest, h56, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_north, advanceAt82_west, advanceAt82_northWest, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, cornerAt82_northWest, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover78 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .southEast = some outcome) : OracleCovered rowCases78 p outcome := by
  cases h82 : p 82 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_south, advanceAt82_east, advanceAt82_southEast, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, cornerAt82_southEast, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_south, advanceAt82_east, advanceAt82_southEast, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, cornerAt82_southEast, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover79 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .southWest = some outcome) : OracleCovered rowCases79 p outcome := by
  cases h82 : p 82 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_south, advanceAt82_west, advanceAt82_southWest, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, cornerAt82_southWest, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 82 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt82_south, advanceAt82_west, advanceAt82_southWest, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, cornerAt82_southWest, h82, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover80 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .north = some outcome) : OracleCovered rowCases80 p outcome := by
  cases h105 : p 105 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt1_north, advanceAt27_north, advanceAt53_north, advanceAt79_north, advanceAt79_south, advanceAt105_north, floorAt1, doorAt1, trapAt1, boxAt1, holeAt1, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, cornerAt105_north, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt1_north, advanceAt27_north, advanceAt53_north, advanceAt79_north, advanceAt79_south, advanceAt105_north, floorAt1, doorAt1, trapAt1, boxAt1, holeAt1, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, cornerAt105_north, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover81 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .south = some outcome) : OracleCovered rowCases81 p outcome := by
  cases h105 : p 105 with
  | false =>
    cases h131 : p 131 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .south = some (.walk 131) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt131_north, advanceAt131_south, advanceAt157_south, advanceAt183_south, advanceAt209_south, advanceAt235_south, advanceAt261_south, advanceAt287_south, advanceAt313_south, advanceAt339_south, advanceAt365_south, advanceAt391_south, advanceAt417_south, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt417, doorAt417, trapAt417, boxAt417, holeAt417, cornerAt105_south, h105, h131, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case031.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case031, memberCase031, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame031.bindings p
      intro binding member
      simp only [frame031, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h105
      · exact h131
    | true =>
      cases h157 : p 157 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .south = some (.push 131 (.stay 157)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt131_north, advanceAt131_south, advanceAt157_south, advanceAt183_south, advanceAt209_south, advanceAt235_south, advanceAt261_south, advanceAt287_south, advanceAt313_south, advanceAt339_south, advanceAt365_south, advanceAt391_south, advanceAt417_south, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt417, doorAt417, trapAt417, boxAt417, holeAt417, cornerAt105_south, h105, h131, h157, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case683.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case683, memberCase683, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame683.bindings p
        intro binding member
        simp only [frame683, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h105
        · exact h131
        · exact h157
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt131_north, advanceAt131_south, advanceAt157_south, advanceAt183_south, advanceAt209_south, advanceAt235_south, advanceAt261_south, advanceAt287_south, advanceAt313_south, advanceAt339_south, advanceAt365_south, advanceAt391_south, advanceAt417_south, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt417, doorAt417, trapAt417, boxAt417, holeAt417, cornerAt105_south, h105, h131, h157, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_south, advanceAt131_north, advanceAt131_south, advanceAt157_south, advanceAt183_south, advanceAt209_south, advanceAt235_south, advanceAt261_south, advanceAt287_south, advanceAt313_south, advanceAt339_south, advanceAt365_south, advanceAt391_south, advanceAt417_south, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt235, doorAt235, trapAt235, boxAt235, holeAt235, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt417, doorAt417, trapAt417, boxAt417, holeAt417, cornerAt105_south, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover82 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .east = some outcome) : OracleCovered rowCases82 p outcome := by
  cases h105 : p 105 with
  | false =>
    cases h106 : p 106 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .east = some (.walk 106) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_east, advanceAt106_east, advanceAt106_west, advanceAt107_east, advanceAt108_east, advanceAt109_east, advanceAt110_east, advanceAt111_east, advanceAt112_east, advanceAt113_east, advanceAt114_east, advanceAt115_east, advanceAt116_east, advanceAt117_east, advanceAt118_east, advanceAt119_east, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, cornerAt105_east, h105, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case032.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case032, memberCase032, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame032.bindings p
      intro binding member
      simp only [frame032, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h105
      · exact h106
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_east, advanceAt106_east, advanceAt106_west, advanceAt107_east, advanceAt108_east, advanceAt109_east, advanceAt110_east, advanceAt111_east, advanceAt112_east, advanceAt113_east, advanceAt114_east, advanceAt115_east, advanceAt116_east, advanceAt117_east, advanceAt118_east, advanceAt119_east, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, cornerAt105_east, h105, h106, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt105_east, advanceAt106_east, advanceAt106_west, advanceAt107_east, advanceAt108_east, advanceAt109_east, advanceAt110_east, advanceAt111_east, advanceAt112_east, advanceAt113_east, advanceAt114_east, advanceAt115_east, advanceAt116_east, advanceAt117_east, advanceAt118_east, advanceAt119_east, advanceAt120_east, advanceAt121_east, advanceAt122_east, advanceAt123_east, advanceAt124_east, advanceAt125_east, advanceAt126_east, advanceAt127_east, advanceAt128_east, advanceAt129_east, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt119, doorAt119, trapAt119, boxAt119, holeAt119, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt121, doorAt121, trapAt121, boxAt121, holeAt121, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt124, doorAt124, trapAt124, boxAt124, holeAt124, floorAt125, doorAt125, trapAt125, boxAt125, holeAt125, floorAt126, doorAt126, trapAt126, boxAt126, holeAt126, floorAt127, doorAt127, trapAt127, boxAt127, holeAt127, floorAt128, doorAt128, trapAt128, boxAt128, holeAt128, floorAt129, doorAt129, trapAt129, boxAt129, holeAt129, cornerAt105_east, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover83 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .west = some outcome) : OracleCovered rowCases83 p outcome := by
  cases h105 : p 105 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_east, advanceAt104_west, advanceAt105_west, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, cornerAt105_west, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 105 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt104_east, advanceAt104_west, advanceAt105_west, floorAt104, doorAt104, trapAt104, boxAt104, holeAt104, floorAt105, doorAt105, trapAt105, boxAt105, holeAt105, cornerAt105_west, h105, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P04
