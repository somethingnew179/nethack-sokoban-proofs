import NetHack.Soko22Hazard87.OracleCover002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover105 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .south = some outcome) :
    OracleCovered rowCases105 p outcome := by
  cases h67 : p 67 with
  | false =>
    cases h89 : p 89 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .south = some (.walk 89) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_south, advanceAt89_north, advanceAt89_south, advanceAt111_south, advanceAt133_south, advanceAt155_south, advanceAt177_south, advanceAt199_south, advanceAt221_south, advanceAt243_south, advanceAt265_south, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt67_south, h67, h89, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 89) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 89), d67301), oracleMember90, same, ?_⟩
      simp only [d57573, d67301, d0, d1, h67, h89, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h111 : p 111 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .south = some (.push 89 (.stay 111)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_south, advanceAt89_north, advanceAt89_south, advanceAt111_south, advanceAt133_south, advanceAt155_south, advanceAt177_south, advanceAt199_south, advanceAt221_south, advanceAt243_south, advanceAt265_south, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt67_south, h67, h89, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 89 (.stay 111)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 89 (.stay 111)), d67924), oracleMember91, same, ?_⟩
        simp only [d57572, d67923, d67924, d0, d1, h67, h89, h111, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_south, advanceAt89_north, advanceAt89_south, advanceAt111_south, advanceAt133_south, advanceAt155_south, advanceAt177_south, advanceAt199_south, advanceAt221_south, advanceAt243_south, advanceAt265_south, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt67_south, h67, h89, h111, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_south, advanceAt89_north, advanceAt89_south, advanceAt111_south, advanceAt133_south, advanceAt155_south, advanceAt177_south, advanceAt199_south, advanceAt221_south, advanceAt243_south, advanceAt265_south, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt67_south, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover106 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .east = some outcome) :
    OracleCovered rowCases106 p outcome := by
  cases h67 : p 67 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_east, advanceAt68_east, advanceAt68_west, advanceAt69_east, advanceAt70_east, advanceAt71_east, advanceAt72_east, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt67_east, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_east, advanceAt68_east, advanceAt68_west, advanceAt69_east, advanceAt70_east, advanceAt71_east, advanceAt72_east, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt67_east, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover107 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .west = some outcome) :
    OracleCovered rowCases107 p outcome := by
  cases h67 : p 67 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_east, advanceAt66_west, advanceAt67_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, cornerAt67_west, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_east, advanceAt66_west, advanceAt67_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, cornerAt67_west, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover108 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .northEast = some outcome) :
    OracleCovered rowCases108 p outcome := by
  cases h67 : p 67 with
  | false =>
    cases h45 : p 45 with
    | false =>
      cases h46 : p 46 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .northEast = some (.walk 46) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_north, advanceAt67_east, advanceAt67_northEast, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, cornerAt67_northEast, h45, h46, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 46) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 46), d58745), oracleMember92, same, ?_⟩
        simp only [d57570, d58744, d58745, d0, d1, h45, h46, h67, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_north, advanceAt67_east, advanceAt67_northEast, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, cornerAt67_northEast, h45, h46, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_north, advanceAt67_east, advanceAt67_northEast, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, cornerAt67_northEast, h45, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_north, advanceAt67_east, advanceAt67_northEast, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, cornerAt67_northEast, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover109 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .northWest = some outcome) :
    OracleCovered rowCases109 p outcome := by
  cases h67 : p 67 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_north, advanceAt67_west, advanceAt67_northWest, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, cornerAt67_northWest, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_north, advanceAt67_west, advanceAt67_northWest, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, cornerAt67_northWest, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover110 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .southEast = some outcome) :
    OracleCovered rowCases110 p outcome := by
  cases h67 : p 67 with
  | false =>
    cases h89 : p 89 with
    | false =>
      cases h90 : p 90 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .southEast = some (.walk 90) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_south, advanceAt67_east, advanceAt67_southEast, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, cornerAt67_southEast, h67, h89, h90, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 90) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 90), d68223), oracleMember93, same, ?_⟩
        simp only [d68221, d68222, d68223, d0, d1, h67, h89, h90, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_south, advanceAt67_east, advanceAt67_southEast, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, cornerAt67_southEast, h67, h89, h90, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_south, advanceAt67_east, advanceAt67_southEast, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, cornerAt67_southEast, h67, h89, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_south, advanceAt67_east, advanceAt67_southEast, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, cornerAt67_southEast, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover111 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .southWest = some outcome) :
    OracleCovered rowCases111 p outcome := by
  cases h67 : p 67 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_south, advanceAt67_west, advanceAt67_southWest, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, cornerAt67_southWest, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt67_south, advanceAt67_west, advanceAt67_southWest, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, cornerAt67_southWest, h67, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover112 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .north = some outcome) :
    OracleCovered rowCases112 p outcome := by
  cases h69 : p 69 with
  | false =>
    cases h47 : p 47 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .north = some (.walk 47) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt25_north, advanceAt47_north, advanceAt47_south, advanceAt69_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt69_north, h47, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 47) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 47), d58432), oracleMember94, same, ?_⟩
      simp only [d53867, d58432, d0, d1, h47, h69, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h25 : p 25 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .north = some (.push 47 (.stay 25)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt25_north, advanceAt47_north, advanceAt47_south, advanceAt69_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt69_north, h25, h47, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 47 (.stay 25)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 47 (.stay 25)), d53870), oracleMember95, same, ?_⟩
        simp only [d53867, d53869, d53870, d0, d1, h25, h47, h69, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt25_north, advanceAt47_north, advanceAt47_south, advanceAt69_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt69_north, h25, h47, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt25_north, advanceAt47_north, advanceAt47_south, advanceAt69_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt69_north, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover113 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .south = some outcome) :
    OracleCovered rowCases113 p outcome := by
  cases h69 : p 69 with
  | false =>
    cases h91 : p 91 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .south = some (.walk 91) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_south, advanceAt91_north, advanceAt91_south, advanceAt113_south, advanceAt135_south, advanceAt157_south, advanceAt179_south, advanceAt201_south, advanceAt223_south, advanceAt245_south, advanceAt267_south, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt69_south, h69, h91, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 91) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 91), d68751), oracleMember96, same, ?_⟩
      simp only [d58747, d68751, d0, d1, h69, h91, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h113 : p 113 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .south = some (.push 91 (.stay 113)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_south, advanceAt91_north, advanceAt91_south, advanceAt113_south, advanceAt135_south, advanceAt157_south, advanceAt179_south, advanceAt201_south, advanceAt223_south, advanceAt245_south, advanceAt267_south, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt69_south, h69, h91, h113, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 91 (.stay 113)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 91 (.stay 113)), d70148), oracleMember97, same, ?_⟩
        simp only [d70145, d70147, d70148, d0, d1, h69, h91, h113, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_south, advanceAt91_north, advanceAt91_south, advanceAt113_south, advanceAt135_south, advanceAt157_south, advanceAt179_south, advanceAt201_south, advanceAt223_south, advanceAt245_south, advanceAt267_south, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt69_south, h69, h91, h113, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_south, advanceAt91_north, advanceAt91_south, advanceAt113_south, advanceAt135_south, advanceAt157_south, advanceAt179_south, advanceAt201_south, advanceAt223_south, advanceAt245_south, advanceAt267_south, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt69_south, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover114 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .east = some outcome) :
    OracleCovered rowCases114 p outcome := by
  cases h69 : p 69 with
  | false =>
    cases h70 : p 70 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .east = some (.walk 70) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_east, advanceAt70_east, advanceAt70_west, advanceAt71_east, advanceAt72_east, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt69_east, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 70) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 70), d61358), oracleMember98, same, ?_⟩
      simp only [d61357, d61358, d0, d1, h69, h70, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h71 : p 71 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .east = some (.push 70 (.stay 71)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_east, advanceAt70_east, advanceAt70_west, advanceAt71_east, advanceAt72_east, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt69_east, h69, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 70 (.stay 71)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 70 (.stay 71)), d72603), oracleMember99, same, ?_⟩
        simp only [d54978, d72602, d72603, d0, d1, h69, h70, h71, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_east, advanceAt70_east, advanceAt70_west, advanceAt71_east, advanceAt72_east, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt69_east, h69, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_east, advanceAt70_east, advanceAt70_west, advanceAt71_east, advanceAt72_east, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt69_east, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover115 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .west = some outcome) :
    OracleCovered rowCases115 p outcome := by
  cases h69 : p 69 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_east, advanceAt68_west, advanceAt69_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt69_west, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_east, advanceAt68_west, advanceAt69_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt69_west, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover116 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .northEast = some outcome) :
    OracleCovered rowCases116 p outcome := by
  cases h69 : p 69 with
  | false =>
    cases h47 : p 47 with
    | false =>
      cases h48 : p 48 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .northEast = some (.walk 48) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_north, advanceAt69_east, advanceAt69_northEast, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt69_northEast, h47, h48, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 48) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 48), d62827), oracleMember100, same, ?_⟩
        simp only [d53867, d61357, d61358, d62825, d62826, d62827, d0, d1, h47, h48, h69, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_north, advanceAt69_east, advanceAt69_northEast, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt69_northEast, h47, h48, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h70 : p 70 with
      | false =>
        cases h48 : p 48 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .northEast = some (.walk 48) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_north, advanceAt69_east, advanceAt69_northEast, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt69_northEast, h47, h48, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 48) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 48), d62827), oracleMember100, same, ?_⟩
          simp only [d53867, d61357, d61358, d62825, d62826, d62827, d0, d1, h47, h48, h69, h70, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_north, advanceAt69_east, advanceAt69_northEast, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt69_northEast, h47, h48, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_north, advanceAt69_east, advanceAt69_northEast, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt69_northEast, h47, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_north, advanceAt69_east, advanceAt69_northEast, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt69_northEast, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover117 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .northWest = some outcome) :
    OracleCovered rowCases117 p outcome := by
  cases h69 : p 69 with
  | false =>
    cases h47 : p 47 with
    | false =>
      cases h46 : p 46 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .northWest = some (.walk 46) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_north, advanceAt69_west, advanceAt69_northWest, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt69_northWest, h46, h47, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 46) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 46), d58433), oracleMember101, same, ?_⟩
        simp only [d53867, d58432, d58433, d0, d1, h46, h47, h69, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_north, advanceAt69_west, advanceAt69_northWest, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt69_northWest, h46, h47, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_north, advanceAt69_west, advanceAt69_northWest, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt69_northWest, h47, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_north, advanceAt69_west, advanceAt69_northWest, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, cornerAt69_northWest, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover118 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .southEast = some outcome) :
    OracleCovered rowCases118 p outcome := by
  cases h69 : p 69 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_south, advanceAt69_east, advanceAt69_southEast, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, cornerAt69_southEast, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_south, advanceAt69_east, advanceAt69_southEast, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, cornerAt69_southEast, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover119 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .southWest = some outcome) :
    OracleCovered rowCases119 p outcome := by
  cases h69 : p 69 with
  | false =>
    cases h91 : p 91 with
    | false =>
      cases h90 : p 90 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .southWest = some (.walk 90) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_south, advanceAt69_west, advanceAt69_southWest, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, cornerAt69_southWest, h69, h90, h91, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 90) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 90), d73191), oracleMember102, same, ?_⟩
        simp only [d58747, d73190, d73191, d0, d1, h69, h90, h91, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_south, advanceAt69_west, advanceAt69_southWest, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, cornerAt69_southWest, h69, h90, h91, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_south, advanceAt69_west, advanceAt69_southWest, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, cornerAt69_southWest, h69, h91, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt69_south, advanceAt69_west, advanceAt69_southWest, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt90, doorAt90, trapAt90, boxAt90, holeAt90, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, cornerAt69_southWest, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover120 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .north = some outcome) :
    OracleCovered rowCases120 p outcome := by
  cases h70 : p 70 with
  | false =>
    cases h48 : p 48 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .north = some (.walk 48) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt48_north, advanceAt48_south, advanceAt70_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt70_north, h48, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 48) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 48), d61807), oracleMember103, same, ?_⟩
      simp only [d61357, d61807, d0, d1, h48, h70, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt48_north, advanceAt48_south, advanceAt70_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt70_north, h48, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt26_north, advanceAt48_north, advanceAt48_south, advanceAt70_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt70_north, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover121 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .south = some outcome) :
    OracleCovered rowCases121 p outcome := by
  cases h70 : p 70 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_south, advanceAt92_north, advanceAt92_south, advanceAt114_south, advanceAt136_south, advanceAt158_south, advanceAt180_south, advanceAt202_south, advanceAt224_south, advanceAt246_south, advanceAt268_south, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt70_south, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_south, advanceAt92_north, advanceAt92_south, advanceAt114_south, advanceAt136_south, advanceAt158_south, advanceAt180_south, advanceAt202_south, advanceAt224_south, advanceAt246_south, advanceAt268_south, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt246, doorAt246, trapAt246, boxAt246, holeAt246, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, cornerAt70_south, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover122 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .east = some outcome) :
    OracleCovered rowCases122 p outcome := by
  cases h70 : p 70 with
  | false =>
    cases h71 : p 71 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .east = some (.walk 71) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_east, advanceAt71_east, advanceAt71_west, advanceAt72_east, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt70_east, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 71) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 71), d62374), oracleMember104, same, ?_⟩
      simp only [d54978, d62374, d0, d1, h70, h71, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_east, advanceAt71_east, advanceAt71_west, advanceAt72_east, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt70_east, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_east, advanceAt71_east, advanceAt71_west, advanceAt72_east, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt70_east, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover123 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .west = some outcome) :
    OracleCovered rowCases123 p outcome := by
  cases h70 : p 70 with
  | false =>
    cases h69 : p 69 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .west = some (.walk 69) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_east, advanceAt69_west, advanceAt70_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt70_west, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 69) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 69), d61358), oracleMember105, same, ?_⟩
      simp only [d61357, d61358, d0, d1, h69, h70, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_east, advanceAt69_west, advanceAt70_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt70_west, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_east, advanceAt69_west, advanceAt70_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt70_west, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover124 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northEast = some outcome) :
    OracleCovered rowCases124 p outcome := by
  cases h70 : p 70 with
  | false =>
    cases h48 : p 48 with
    | false =>
      cases h49 : p 49 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northEast = some (.walk 49) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_north, advanceAt70_east, advanceAt70_northEast, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt70_northEast, h48, h49, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 49) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 49), d64542), oracleMember106, same, ?_⟩
        simp only [d54978, d61357, d62374, d64540, d64541, d64542, d0, d1, h48, h49, h70, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_north, advanceAt70_east, advanceAt70_northEast, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt70_northEast, h48, h49, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h71 : p 71 with
      | false =>
        cases h49 : p 49 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northEast = some (.walk 49) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_north, advanceAt70_east, advanceAt70_northEast, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt70_northEast, h48, h49, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 49) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 49), d64542), oracleMember106, same, ?_⟩
          simp only [d54978, d61357, d62374, d64540, d64541, d64542, d0, d1, h48, h49, h70, h71, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_north, advanceAt70_east, advanceAt70_northEast, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt70_northEast, h48, h49, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_north, advanceAt70_east, advanceAt70_northEast, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt70_northEast, h48, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_north, advanceAt70_east, advanceAt70_northEast, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt70_northEast, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover125 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northWest = some outcome) :
    OracleCovered rowCases125 p outcome := by
  cases h70 : p 70 with
  | false =>
    cases h48 : p 48 with
    | false =>
      cases h47 : p 47 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northWest = some (.walk 47) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_north, advanceAt70_west, advanceAt70_northWest, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt70_northWest, h47, h48, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 47) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 47), d61360), oracleMember107, same, ?_⟩
        simp only [d61357, d61358, d61359, d61360, d0, d1, h47, h48, h70, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_north, advanceAt70_west, advanceAt70_northWest, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt70_northWest, h47, h48, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h69 : p 69 with
      | false =>
        cases h47 : p 47 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northWest = some (.walk 47) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_north, advanceAt70_west, advanceAt70_northWest, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt70_northWest, h47, h48, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 47) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 47), d61360), oracleMember107, same, ?_⟩
          simp only [d61357, d61358, d61359, d61360, d0, d1, h47, h48, h69, h70, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_north, advanceAt70_west, advanceAt70_northWest, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt70_northWest, h47, h48, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_north, advanceAt70_west, advanceAt70_northWest, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt70_northWest, h48, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_north, advanceAt70_west, advanceAt70_northWest, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, cornerAt70_northWest, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover126 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .southEast = some outcome) :
    OracleCovered rowCases126 p outcome := by
  cases h70 : p 70 with
  | false =>
    cases h71 : p 71 with
    | false =>
      cases h93 : p 93 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .southEast = some (.walk 93) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_south, advanceAt70_east, advanceAt70_southEast, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, cornerAt70_southEast, h70, h71, h93, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 93) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 93), d73493), oracleMember108, same, ?_⟩
        simp only [d62936, d73492, d73493, d0, d1, h70, h71, h93, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_south, advanceAt70_east, advanceAt70_southEast, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, cornerAt70_southEast, h70, h71, h93, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_south, advanceAt70_east, advanceAt70_southEast, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, cornerAt70_southEast, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_south, advanceAt70_east, advanceAt70_southEast, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, cornerAt70_southEast, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover127 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .southWest = some outcome) :
    OracleCovered rowCases127 p outcome := by
  cases h70 : p 70 with
  | false =>
    cases h69 : p 69 with
    | false =>
      cases h91 : p 91 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .southWest = some (.walk 91) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_south, advanceAt70_west, advanceAt70_southWest, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, cornerAt70_southWest, h69, h70, h91, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 91) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 91), d73495), oracleMember109, same, ?_⟩
        simp only [d58747, d73494, d73495, d0, d1, h69, h70, h91, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_south, advanceAt70_west, advanceAt70_southWest, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, cornerAt70_southWest, h69, h70, h91, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_south, advanceAt70_west, advanceAt70_southWest, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, cornerAt70_southWest, h69, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt70_south, advanceAt70_west, advanceAt70_southWest, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, cornerAt70_southWest, h70, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover128 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .north = some outcome) :
    OracleCovered rowCases128 p outcome := by
  cases h71 : p 71 with
  | false =>
    cases h49 : p 49 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .north = some (.walk 49) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt27_north, advanceAt49_north, advanceAt49_south, advanceAt71_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_north, h49, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 49) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 49), d62934), oracleMember110, same, ?_⟩
      simp only [d54978, d62934, d0, d1, h49, h71, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h27 : p 27 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .north = some (.push 49 (.stay 27)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt27_north, advanceAt49_north, advanceAt49_south, advanceAt71_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_north, h27, h49, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 49 (.stay 27)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 49 (.stay 27)), d54981), oracleMember111, same, ?_⟩
        simp only [d54978, d54980, d54981, d0, d1, h27, h49, h71, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt27_north, advanceAt49_north, advanceAt49_south, advanceAt71_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_north, h27, h49, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt27_north, advanceAt49_north, advanceAt49_south, advanceAt71_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_north, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover129 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .south = some outcome) :
    OracleCovered rowCases129 p outcome := by
  cases h71 : p 71 with
  | false =>
    cases h93 : p 93 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .south = some (.walk 93) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_south, advanceAt93_north, advanceAt93_south, advanceAt115_south, advanceAt137_south, advanceAt159_south, advanceAt181_south, advanceAt203_south, advanceAt225_south, advanceAt247_south, advanceAt269_south, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt71_south, h71, h93, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 93) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 93), d73492), oracleMember112, same, ?_⟩
      simp only [d62936, d73492, d0, d1, h71, h93, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h115 : p 115 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .south = some (.push 93 (.stay 115)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_south, advanceAt93_north, advanceAt93_south, advanceAt115_south, advanceAt137_south, advanceAt159_south, advanceAt181_south, advanceAt203_south, advanceAt225_south, advanceAt247_south, advanceAt269_south, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt71_south, h71, h93, h115, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 93 (.stay 115)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 93 (.stay 115)), d73777), oracleMember113, same, ?_⟩
        simp only [d73774, d73776, d73777, d0, d1, h71, h93, h115, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_south, advanceAt93_north, advanceAt93_south, advanceAt115_south, advanceAt137_south, advanceAt159_south, advanceAt181_south, advanceAt203_south, advanceAt225_south, advanceAt247_south, advanceAt269_south, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt71_south, h71, h93, h115, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_south, advanceAt93_north, advanceAt93_south, advanceAt115_south, advanceAt137_south, advanceAt159_south, advanceAt181_south, advanceAt203_south, advanceAt225_south, advanceAt247_south, advanceAt269_south, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt71_south, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover130 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .east = some outcome) :
    OracleCovered rowCases130 p outcome := by
  cases h71 : p 71 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_east, advanceAt72_east, advanceAt72_west, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt71_east, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_east, advanceAt72_east, advanceAt72_west, advanceAt73_east, advanceAt74_east, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt71_east, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover131 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .west = some outcome) :
    OracleCovered rowCases131 p outcome := by
  cases h71 : p 71 with
  | false =>
    cases h70 : p 70 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .west = some (.walk 70) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_east, advanceAt70_west, advanceAt71_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_west, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 70) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 70), d62374), oracleMember114, same, ?_⟩
      simp only [d54978, d62374, d0, d1, h70, h71, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h69 : p 69 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .west = some (.push 70 (.stay 69)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_east, advanceAt70_west, advanceAt71_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_west, h69, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 70 (.stay 69)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 70 (.stay 69)), d72603), oracleMember115, same, ?_⟩
        simp only [d54978, d72602, d72603, d0, d1, h69, h70, h71, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_east, advanceAt70_west, advanceAt71_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_west, h69, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_east, advanceAt70_west, advanceAt71_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_west, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover132 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .northEast = some outcome) :
    OracleCovered rowCases132 p outcome := by
  cases h71 : p 71 with
  | false =>
    cases h49 : p 49 with
    | false =>
      cases h50 : p 50 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .northEast = some (.walk 50) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_north, advanceAt71_east, advanceAt71_northEast, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, cornerAt71_northEast, h49, h50, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 50) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 50), d64965), oracleMember116, same, ?_⟩
        simp only [d54978, d64964, d64965, d0, d1, h49, h50, h71, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_north, advanceAt71_east, advanceAt71_northEast, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, cornerAt71_northEast, h49, h50, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_north, advanceAt71_east, advanceAt71_northEast, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, cornerAt71_northEast, h49, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_north, advanceAt71_east, advanceAt71_northEast, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, cornerAt71_northEast, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover133 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .northWest = some outcome) :
    OracleCovered rowCases133 p outcome := by
  cases h71 : p 71 with
  | false =>
    cases h49 : p 49 with
    | false =>
      cases h48 : p 48 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .northWest = some (.walk 48) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_north, advanceAt71_west, advanceAt71_northWest, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_northWest, h48, h49, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 48) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 48), d62376), oracleMember117, same, ?_⟩
        simp only [d54978, d62374, d62375, d62376, d0, d1, h48, h49, h71, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_north, advanceAt71_west, advanceAt71_northWest, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_northWest, h48, h49, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h70 : p 70 with
      | false =>
        cases h48 : p 48 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .northWest = some (.walk 48) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_north, advanceAt71_west, advanceAt71_northWest, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_northWest, h48, h49, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 48) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 48), d62376), oracleMember117, same, ?_⟩
          simp only [d54978, d62374, d62375, d62376, d0, d1, h48, h49, h70, h71, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_north, advanceAt71_west, advanceAt71_northWest, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_northWest, h48, h49, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_north, advanceAt71_west, advanceAt71_northWest, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_northWest, h49, h70, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_north, advanceAt71_west, advanceAt71_northWest, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, cornerAt71_northWest, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover134 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .southEast = some outcome) :
    OracleCovered rowCases134 p outcome := by
  cases h71 : p 71 with
  | false =>
    cases h93 : p 93 with
    | false =>
      cases h94 : p 94 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .southEast = some (.walk 94) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_south, advanceAt71_east, advanceAt71_southEast, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, cornerAt71_southEast, h71, h93, h94, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 94) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 94), d74039), oracleMember118, same, ?_⟩
        simp only [d62936, d73492, d74039, d0, d1, h71, h93, h94, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_south, advanceAt71_east, advanceAt71_southEast, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, cornerAt71_southEast, h71, h93, h94, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_south, advanceAt71_east, advanceAt71_southEast, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, cornerAt71_southEast, h71, h93, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_south, advanceAt71_east, advanceAt71_southEast, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, cornerAt71_southEast, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover135 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .southWest = some outcome) :
    OracleCovered rowCases135 p outcome := by
  cases h71 : p 71 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_south, advanceAt71_west, advanceAt71_southWest, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, cornerAt71_southWest, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt71_south, advanceAt71_west, advanceAt71_southWest, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt92, doorAt92, trapAt92, boxAt92, holeAt92, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, cornerAt71_southWest, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover136 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .north = some outcome) :
    OracleCovered rowCases136 p outcome := by
  cases h73 : p 73 with
  | false =>
    cases h51 : p 51 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .north = some (.walk 51) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt29_north, advanceAt51_north, advanceAt51_south, advanceAt73_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, cornerAt73_north, h51, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 51) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 51), d64793), oracleMember119, same, ?_⟩
      simp only [d56150, d64793, d0, d1, h51, h73, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h29 : p 29 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .north = some (.push 51 (.stay 29)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt29_north, advanceAt51_north, advanceAt51_south, advanceAt73_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, cornerAt73_north, h29, h51, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 51 (.stay 29)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 51 (.stay 29)), d56153), oracleMember120, same, ?_⟩
        simp only [d56150, d56152, d56153, d0, d1, h29, h51, h73, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt29_north, advanceAt51_north, advanceAt51_south, advanceAt73_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, cornerAt73_north, h29, h51, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt29_north, advanceAt51_north, advanceAt51_south, advanceAt73_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, cornerAt73_north, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover137 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .south = some outcome) :
    OracleCovered rowCases137 p outcome := by
  cases h73 : p 73 with
  | false =>
    cases h95 : p 95 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .south = some (.walk 95) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt95_north, advanceAt95_south, advanceAt117_south, advanceAt139_south, advanceAt161_south, advanceAt183_south, advanceAt205_south, advanceAt227_south, advanceAt249_south, advanceAt271_south, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt73_south, h73, h95, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 95) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 95), d74040), oracleMember121, same, ?_⟩
      simp only [d65087, d74040, d0, d1, h73, h95, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt95_north, advanceAt95_south, advanceAt117_south, advanceAt139_south, advanceAt161_south, advanceAt183_south, advanceAt205_south, advanceAt227_south, advanceAt249_south, advanceAt271_south, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt73_south, h73, h95, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_south, advanceAt95_north, advanceAt95_south, advanceAt117_south, advanceAt139_south, advanceAt161_south, advanceAt183_south, advanceAt205_south, advanceAt227_south, advanceAt249_south, advanceAt271_south, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt73_south, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover138 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .east = some outcome) :
    OracleCovered rowCases138 p outcome := by
  cases h73 : p 73 with
  | false =>
    cases h74 : p 74 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .east = some (.walk 74) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_east, advanceAt74_east, advanceAt74_west, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt73_east, h73, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 74) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 74), d66089), oracleMember122, same, ?_⟩
      simp only [d56773, d66089, d0, d1, h73, h74, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_east, advanceAt74_east, advanceAt74_west, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt73_east, h73, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt73_east, advanceAt74_east, advanceAt74_west, advanceAt75_east, advanceAt76_east, advanceAt77_east, advanceAt78_east, advanceAt79_east, advanceAt80_east, advanceAt81_east, advanceAt82_east, advanceAt83_east, advanceAt84_east, advanceAt85_east, advanceAt86_east, advanceAt87_east, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt75, doorAt75, trapAt75, boxAt75, holeAt75, floorAt76, doorAt76, trapAt76, boxAt76, holeAt76, floorAt77, doorAt77, trapAt77, boxAt77, holeAt77, floorAt78, doorAt78, trapAt78, boxAt78, holeAt78, floorAt79, doorAt79, trapAt79, boxAt79, holeAt79, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, cornerAt73_east, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover139 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .west = some outcome) :
    OracleCovered rowCases139 p outcome := by
  cases h73 : p 73 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_west, advanceAt71_west, advanceAt72_east, advanceAt72_west, advanceAt73_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, cornerAt73_west, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt66_west, advanceAt67_west, advanceAt68_west, advanceAt69_west, advanceAt70_west, advanceAt71_west, advanceAt72_east, advanceAt72_west, advanceAt73_west, floorAt66, doorAt66, trapAt66, boxAt66, holeAt66, floorAt67, doorAt67, trapAt67, boxAt67, holeAt67, floorAt68, doorAt68, trapAt68, boxAt68, holeAt68, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt70, doorAt70, trapAt70, boxAt70, holeAt70, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, cornerAt73_west, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko22Hazard87
