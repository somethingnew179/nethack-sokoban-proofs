import NetHack.Soko22Hazard87.OracleCover003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover140 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .northEast = some outcome) :
    OracleCovered rowCases140 p outcome := by
  cases h73 : p 73 with
  | false =>
    cases h51 : p 51 with
    | false =>
      cases h52 : p 52 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .northEast = some (.walk 52) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_north, advanceAt73_east, advanceAt73_northEast, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt73_northEast, h51, h52, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 52) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 52), d67300), oracleMember123, same, ?_⟩
        simp only [d56150, d56773, d66089, d67299, d67300, d0, d1, h51, h52, h73, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_north, advanceAt73_east, advanceAt73_northEast, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt73_northEast, h51, h52, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h74 : p 74 with
      | false =>
        cases h52 : p 52 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .northEast = some (.walk 52) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_north, advanceAt73_east, advanceAt73_northEast, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt73_northEast, h51, h52, h73, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 52) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 52), d67300), oracleMember123, same, ?_⟩
          simp only [d56150, d56773, d66089, d67299, d67300, d0, d1, h51, h52, h73, h74, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_north, advanceAt73_east, advanceAt73_northEast, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt73_northEast, h51, h52, h73, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_north, advanceAt73_east, advanceAt73_northEast, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt73_northEast, h51, h73, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_north, advanceAt73_east, advanceAt73_northEast, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt73_northEast, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover141 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .northWest = some outcome) :
    OracleCovered rowCases141 p outcome := by
  cases h73 : p 73 with
  | false =>
    cases h51 : p 51 with
    | false =>
      cases h50 : p 50 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .northWest = some (.walk 50) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_north, advanceAt73_west, advanceAt73_northWest, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, cornerAt73_northWest, h50, h51, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 50) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 50), d64794), oracleMember124, same, ?_⟩
        simp only [d56150, d64793, d64794, d0, d1, h50, h51, h73, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_north, advanceAt73_west, advanceAt73_northWest, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, cornerAt73_northWest, h50, h51, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_north, advanceAt73_west, advanceAt73_northWest, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, cornerAt73_northWest, h51, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_north, advanceAt73_west, advanceAt73_northWest, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, cornerAt73_northWest, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover142 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .southEast = some outcome) :
    OracleCovered rowCases142 p outcome := by
  cases h73 : p 73 with
  | false =>
    cases h95 : p 95 with
    | false =>
      cases h96 : p 96 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .southEast = some (.walk 96) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt73_east, advanceAt73_southEast, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, cornerAt73_southEast, h73, h95, h96, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 96) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 96), d74046), oracleMember125, same, ?_⟩
        simp only [d66277, d74044, d74045, d74046, d0, d1, h73, h95, h96, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt73_east, advanceAt73_southEast, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, cornerAt73_southEast, h73, h95, h96, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h74 : p 74 with
      | false =>
        cases h96 : p 96 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .southEast = some (.walk 96) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt73_east, advanceAt73_southEast, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, cornerAt73_southEast, h73, h74, h95, h96, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 96) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 96), d74046), oracleMember125, same, ?_⟩
          simp only [d66277, d74044, d74045, d74046, d0, d1, h73, h74, h95, h96, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt73_east, advanceAt73_southEast, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, cornerAt73_southEast, h73, h74, h95, h96, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt73_east, advanceAt73_southEast, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, cornerAt73_southEast, h73, h74, h95, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt73_east, advanceAt73_southEast, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, cornerAt73_southEast, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover143 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .southWest = some outcome) :
    OracleCovered rowCases143 p outcome := by
  cases h73 : p 73 with
  | false =>
    cases h95 : p 95 with
    | false =>
      cases h94 : p 94 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .southWest = some (.walk 94) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt73_west, advanceAt73_southWest, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, cornerAt73_southWest, h73, h94, h95, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 94) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 94), d74047), oracleMember126, same, ?_⟩
        simp only [d65087, d74040, d74047, d0, d1, h73, h94, h95, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt73_west, advanceAt73_southWest, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, cornerAt73_southWest, h73, h94, h95, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt73_west, advanceAt73_southWest, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, cornerAt73_southWest, h73, h95, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt73_west, advanceAt73_southWest, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, cornerAt73_southWest, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover144 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .north = some outcome) :
    OracleCovered rowCases144 p outcome := by
  cases h74 : p 74 with
  | false =>
    cases h52 : p 52 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .north = some (.walk 52) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt30_north, advanceAt52_north, advanceAt52_south, advanceAt74_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_north, h52, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 52) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 52), d66275), oracleMember127, same, ?_⟩
      simp only [d56773, d66275, d0, d1, h52, h74, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h30 : p 30 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .north = some (.push 52 (.stay 30)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt30_north, advanceAt52_north, advanceAt52_south, advanceAt74_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_north, h30, h52, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 52 (.stay 30)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 52 (.stay 30)), d56776), oracleMember128, same, ?_⟩
        simp only [d56773, d56775, d56776, d0, d1, h30, h52, h74, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt30_north, advanceAt52_north, advanceAt52_south, advanceAt74_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_north, h30, h52, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt30_north, advanceAt52_north, advanceAt52_south, advanceAt74_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_north, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover145 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .south = some outcome) :
    OracleCovered rowCases145 p outcome := by
  cases h74 : p 74 with
  | false =>
    cases h96 : p 96 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .south = some (.walk 96) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt96_north, advanceAt96_south, advanceAt118_south, advanceAt140_south, advanceAt162_south, advanceAt184_south, advanceAt206_south, advanceAt228_south, advanceAt250_south, advanceAt272_south, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt74_south, h74, h96, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 96) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 96), d74048), oracleMember129, same, ?_⟩
      simp only [d66277, d74048, d0, d1, h74, h96, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h118 : p 118 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .south = some (.push 96 (.stay 118)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt96_north, advanceAt96_south, advanceAt118_south, advanceAt140_south, advanceAt162_south, advanceAt184_south, advanceAt206_south, advanceAt228_south, advanceAt250_south, advanceAt272_south, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt74_south, h74, h96, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 96 (.stay 118)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 96 (.stay 118)), d74052), oracleMember130, same, ?_⟩
        simp only [d66276, d74051, d74052, d0, d1, h74, h96, h118, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt96_north, advanceAt96_south, advanceAt118_south, advanceAt140_south, advanceAt162_south, advanceAt184_south, advanceAt206_south, advanceAt228_south, advanceAt250_south, advanceAt272_south, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt74_south, h74, h96, h118, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt96_north, advanceAt96_south, advanceAt118_south, advanceAt140_south, advanceAt162_south, advanceAt184_south, advanceAt206_south, advanceAt228_south, advanceAt250_south, advanceAt272_south, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt74_south, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover146 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .east = some outcome) :
    OracleCovered rowCases146 p outcome := by
  cases h74 : p 74 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_east, advanceAt75_east, advanceAt75_west, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt74_east, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_east, advanceAt75_east, advanceAt75_west, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt74_east, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover147 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .west = some outcome) :
    OracleCovered rowCases147 p outcome := by
  cases h74 : p 74 with
  | false =>
    cases h73 : p 73 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .west = some (.walk 73) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_west, advanceAt71_west, advanceAt72_west, advanceAt73_east, advanceAt73_west, advanceAt74_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_west, h73, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 73) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 73), d66089), oracleMember131, same, ?_⟩
      simp only [d56773, d66089, d0, d1, h73, h74, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_west, advanceAt71_west, advanceAt72_west, advanceAt73_east, advanceAt73_west, advanceAt74_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_west, h73, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_west, advanceAt71_west, advanceAt72_west, advanceAt73_east, advanceAt73_west, advanceAt74_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_west, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover148 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .northEast = some outcome) :
    OracleCovered rowCases148 p outcome := by
  cases h74 : p 74 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_north, advanceAt74_east, advanceAt74_northEast, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, cornerAt74_northEast, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_north, advanceAt74_east, advanceAt74_northEast, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, cornerAt74_northEast, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover149 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .northWest = some outcome) :
    OracleCovered rowCases149 p outcome := by
  cases h74 : p 74 with
  | false =>
    cases h52 : p 52 with
    | false =>
      cases h51 : p 51 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .northWest = some (.walk 51) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_north, advanceAt74_west, advanceAt74_northWest, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_northWest, h51, h52, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 51) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 51), d66091), oracleMember132, same, ?_⟩
        simp only [d56773, d66088, d66089, d66090, d66091, d0, d1, h51, h52, h74, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_north, advanceAt74_west, advanceAt74_northWest, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_northWest, h51, h52, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h73 : p 73 with
      | false =>
        cases h51 : p 51 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .northWest = some (.walk 51) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_north, advanceAt74_west, advanceAt74_northWest, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_northWest, h51, h52, h73, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 51) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 51), d66091), oracleMember132, same, ?_⟩
          simp only [d56773, d66088, d66089, d66090, d66091, d0, d1, h51, h52, h73, h74, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_north, advanceAt74_west, advanceAt74_northWest, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_northWest, h51, h52, h73, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_north, advanceAt74_west, advanceAt74_northWest, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_northWest, h52, h73, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_north, advanceAt74_west, advanceAt74_northWest, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, cornerAt74_northWest, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover150 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .southEast = some outcome) :
    OracleCovered rowCases150 p outcome := by
  cases h74 : p 74 with
  | false =>
    cases h96 : p 96 with
    | false =>
      cases h97 : p 97 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .southEast = some (.walk 97) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt74_east, advanceAt74_southEast, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, cornerAt74_southEast, h74, h96, h97, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 97) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 97), d74056), oracleMember133, same, ?_⟩
        simp only [d66277, d74048, d74056, d0, d1, h74, h96, h97, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt74_east, advanceAt74_southEast, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, cornerAt74_southEast, h74, h96, h97, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt74_east, advanceAt74_southEast, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, cornerAt74_southEast, h74, h96, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt74_east, advanceAt74_southEast, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, cornerAt74_southEast, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover151 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .southWest = some outcome) :
    OracleCovered rowCases151 p outcome := by
  cases h74 : p 74 with
  | false =>
    cases h96 : p 96 with
    | false =>
      cases h95 : p 95 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .southWest = some (.walk 95) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt74_west, advanceAt74_southWest, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, cornerAt74_southWest, h74, h95, h96, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 95) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 95), d74062), oracleMember134, same, ?_⟩
        simp only [d65087, d66277, d74044, d74060, d74061, d74062, d0, d1, h74, h95, h96, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt74_west, advanceAt74_southWest, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, cornerAt74_southWest, h74, h95, h96, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h73 : p 73 with
      | false =>
        cases h95 : p 95 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .southWest = some (.walk 95) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt74_west, advanceAt74_southWest, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, cornerAt74_southWest, h73, h74, h95, h96, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 95) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 95), d74062), oracleMember134, same, ?_⟩
          simp only [d65087, d66277, d74044, d74060, d74061, d74062, d0, d1, h73, h74, h95, h96, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt74_west, advanceAt74_southWest, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, cornerAt74_southWest, h73, h74, h95, h96, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt74_west, advanceAt74_southWest, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, cornerAt74_southWest, h73, h74, h96, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt74_south, advanceAt74_west, advanceAt74_southWest, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, cornerAt74_southWest, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover152 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .north = some outcome) :
    OracleCovered rowCases152 p outcome := by
  cases h76 : p 76 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt32_north, advanceAt54_north, advanceAt54_south, advanceAt76_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, cornerAt76_north, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt32_north, advanceAt54_north, advanceAt54_south, advanceAt76_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, cornerAt76_north, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover153 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .south = some outcome) :
    OracleCovered rowCases153 p outcome := by
  cases h76 : p 76 with
  | false =>
    cases h98 : p 98 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .south = some (.walk 98) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_south, advanceAt98_north, advanceAt98_south, advanceAt120_south, advanceAt142_south, advanceAt164_south, advanceAt186_south, advanceAt208_south, advanceAt230_south, advanceAt252_south, advanceAt274_south, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt76_south, h76, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 98) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 98), d74067), oracleMember135, same, ?_⟩
      simp only [d74066, d74067, d0, d1, h76, h98, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h120 : p 120 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .south = some (.push 98 (.stay 120)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_south, advanceAt98_north, advanceAt98_south, advanceAt120_south, advanceAt142_south, advanceAt164_south, advanceAt186_south, advanceAt208_south, advanceAt230_south, advanceAt252_south, advanceAt274_south, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt76_south, h76, h98, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 98 (.stay 120)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 98 (.stay 120)), d74072), oracleMember136, same, ?_⟩
        simp only [d74069, d74071, d74072, d0, d1, h76, h98, h120, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_south, advanceAt98_north, advanceAt98_south, advanceAt120_south, advanceAt142_south, advanceAt164_south, advanceAt186_south, advanceAt208_south, advanceAt230_south, advanceAt252_south, advanceAt274_south, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt76_south, h76, h98, h120, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_south, advanceAt98_north, advanceAt98_south, advanceAt120_south, advanceAt142_south, advanceAt164_south, advanceAt186_south, advanceAt208_south, advanceAt230_south, advanceAt252_south, advanceAt274_south, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt120, doorAt120, trapAt120, boxAt120, holeAt120, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt252, doorAt252, trapAt252, boxAt252, holeAt252, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, cornerAt76_south, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover154 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .east = some outcome) :
    OracleCovered rowCases154 p outcome := by
  cases h76 : p 76 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_east, advanceAt77_east, advanceAt77_west, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt76_east, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_east, advanceAt77_east, advanceAt77_west, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt76_east, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover155 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .west = some outcome) :
    OracleCovered rowCases155 p outcome := by
  cases h76 : p 76 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_west, advanceAt71_west, advanceAt72_west, advanceAt73_west, advanceAt74_west, advanceAt75_east, advanceAt75_west, advanceAt76_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, cornerAt76_west, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_west, advanceAt71_west, advanceAt72_west, advanceAt73_west, advanceAt74_west, advanceAt75_east, advanceAt75_west, advanceAt76_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, cornerAt76_west, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover156 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .northEast = some outcome) :
    OracleCovered rowCases156 p outcome := by
  cases h76 : p 76 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_north, advanceAt76_east, advanceAt76_northEast, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, cornerAt76_northEast, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_north, advanceAt76_east, advanceAt76_northEast, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, cornerAt76_northEast, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover157 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .northWest = some outcome) :
    OracleCovered rowCases157 p outcome := by
  cases h76 : p 76 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_north, advanceAt76_west, advanceAt76_northWest, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, cornerAt76_northWest, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_north, advanceAt76_west, advanceAt76_northWest, floorAt53, doorAt53, trapAt53, boxAt53, holeAt53, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, cornerAt76_northWest, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover158 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .southEast = some outcome) :
    OracleCovered rowCases158 p outcome := by
  cases h76 : p 76 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_south, advanceAt76_east, advanceAt76_southEast, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, cornerAt76_southEast, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_south, advanceAt76_east, advanceAt76_southEast, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, cornerAt76_southEast, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover159 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .southWest = some outcome) :
    OracleCovered rowCases159 p outcome := by
  cases h76 : p 76 with
  | false =>
    cases h98 : p 98 with
    | false =>
      cases h97 : p 97 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .southWest = some (.walk 97) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_south, advanceAt76_west, advanceAt76_southWest, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt76_southWest, h76, h97, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 97) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 97), d74074), oracleMember137, same, ?_⟩
        simp only [d74066, d74073, d74074, d0, d1, h76, h97, h98, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_south, advanceAt76_west, advanceAt76_southWest, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt76_southWest, h76, h97, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_south, advanceAt76_west, advanceAt76_southWest, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt76_southWest, h76, h98, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt76_south, advanceAt76_west, advanceAt76_southWest, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt97, doorAt97, trapAt97, boxAt97, holeAt97, floorAt98, doorAt98, trapAt98, boxAt98, holeAt98, cornerAt76_southWest, h76, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover160 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .north = some outcome) :
    OracleCovered rowCases160 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .north = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt12_north, advanceAt34_north, advanceAt56_north, advanceAt56_south, advanceAt78_north, floorAt12, doorAt12, trapAt12, boxAt12, holeAt12, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, cornerAt78_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover161 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .south = some outcome) :
    OracleCovered rowCases161 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .south = some (.walk 100) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt78_south, advanceAt100_north, advanceAt100_south, advanceAt122_south, advanceAt144_south, advanceAt166_south, advanceAt188_south, advanceAt210_south, advanceAt232_south, advanceAt254_south, advanceAt276_south, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt122, doorAt122, trapAt122, boxAt122, holeAt122, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt254, doorAt254, trapAt254, boxAt254, holeAt254, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, cornerAt78_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 100) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 100), d1), oracleMember138, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover162 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .east = some outcome) :
    OracleCovered rowCases162 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .east = some (.walk 79) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt78_east, advanceAt79_east, advanceAt79_west, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt78_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 79) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 79), d1), oracleMember140, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover163 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .west = some outcome) :
    OracleCovered rowCases163 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .west = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_west, advanceAt71_west, advanceAt72_west, advanceAt73_west, advanceAt74_west, advanceAt75_west, advanceAt76_west, advanceAt77_east, advanceAt77_west, advanceAt78_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, cornerAt78_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover164 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .northEast = some outcome) :
    OracleCovered rowCases164 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .northEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt78_north, advanceAt78_east, advanceAt78_northEast, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, cornerAt78_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover165 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .northWest = some outcome) :
    OracleCovered rowCases165 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .northWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt78_north, advanceAt78_west, advanceAt78_northWest, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, cornerAt78_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover166 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .southEast = some outcome) :
    OracleCovered rowCases166 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .southEast = some (.walk 101) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt78_south, advanceAt78_east, advanceAt78_southEast, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, cornerAt78_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 101) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 101), d1), oracleMember142, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover167 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .southWest = some outcome) :
    OracleCovered rowCases167 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 .southWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt78_south, advanceAt78_west, advanceAt78_southWest, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt99, doorAt99, trapAt99, boxAt99, holeAt99, floorAt100, doorAt100, trapAt100, boxAt100, holeAt100, cornerAt78_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover168 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .north = some outcome) :
    OracleCovered rowCases168 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .north = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt13_north, advanceAt35_north, advanceAt57_north, advanceAt57_south, advanceAt79_north, floorAt13, doorAt13, trapAt13, boxAt13, holeAt13, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, cornerAt79_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover169 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .south = some outcome) :
    OracleCovered rowCases169 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .south = some (.walk 101) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt79_south, advanceAt101_north, advanceAt101_south, advanceAt123_south, advanceAt145_south, advanceAt167_south, advanceAt189_south, advanceAt211_south, advanceAt233_south, advanceAt255_south, advanceAt277_south, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt123, doorAt123, trapAt123, boxAt123, holeAt123, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, floorAt255, doorAt255, trapAt255, boxAt255, holeAt255, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, cornerAt79_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 101) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 101), d1), oracleMember143, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover170 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .east = some outcome) :
    OracleCovered rowCases170 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .east = some (.walk 80) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt79_east, advanceAt80_east, advanceAt80_west, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt79_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 80) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 80), d1), oracleMember145, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover171 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .west = some outcome) :
    OracleCovered rowCases171 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .west = some (.walk 78) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_west, advanceAt71_west, advanceAt72_west, advanceAt73_west, advanceAt74_west, advanceAt75_west, advanceAt76_west, advanceAt77_west, advanceAt78_east, advanceAt78_west, advanceAt79_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, cornerAt79_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 78) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 78), d1), oracleMember147, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
theorem oracleCover172 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .northEast = some outcome) :
    OracleCovered rowCases172 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .northEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt79_north, advanceAt79_east, advanceAt79_northEast, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, cornerAt79_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover173 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .northWest = some outcome) :
    OracleCovered rowCases173 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .northWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt79_north, advanceAt79_west, advanceAt79_northWest, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, cornerAt79_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover174 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .southEast = some outcome) :
    OracleCovered rowCases174 p outcome := by
  have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 .southEast = some (.walk 102) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt79_south, advanceAt79_east, advanceAt79_southEast, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt101, doorAt101, trapAt101, boxAt101, holeAt101, floorAt102, doorAt102, trapAt102, boxAt102, holeAt102, cornerAt79_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = (.walk 102) := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨((.walk 102), d1), oracleMember148, same, ?_⟩
  simp only [d0, d1, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
end NetHack.Soko22Hazard87
