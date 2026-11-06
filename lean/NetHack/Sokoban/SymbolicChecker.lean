/- Small logical bridges for shared Shannon proof certificates.
No evaluator or foreign solver is trusted for a mathematical decision. -/
import NetHack.Sokoban.PatternChecker
namespace NetHack.Sokoban.PatternCorrection
open LowerBounds

def directionCheck (board : Board) (originalHoles : List Cell) (potential : Potential)
    (support : List Cell) (bonus : Cell → Pattern → Int) (player : Cell)
    (direction : Dir) (pattern : Pattern) : Bool :=
    match advance board player direction with
    | none => true
    | some source =>
      if !board.floor.contains source then true else
      ((!walkGuard board support pattern player source direction ||
        decide (bonus player pattern ≤ bonus source pattern)) &&
      (if direction.diagonal then true else
        match advance board source direction with
        | none => true
        | some first =>
          if !board.floor.contains first then true else
          (PreciseRolling.stayTargets board source direction).all (fun landing =>
            !pushGuard support pattern player source first landing ||
            decide (bonus player pattern ≤ 1 + potential.boulder landing - potential.boulder source +
              bonus source (change pattern source (some landing)))) &&
          (pushTargets board source direction).all (fun landing =>
            !originalHoles.contains landing || !pushGuard support pattern player source first landing ||
            decide (bonus player pattern ≤ 1 - potential.boulder source - potential.hole landing +
              bonus source (change pattern source none)))))

theorem check_of_implication (guard : Bool) (proposition : Prop) [Decidable proposition]
    (proof : guard = true → proposition) : (!guard || decide proposition) = true := by
  cases h : guard with
  | false => rfl
  | true => simpa only [h, Bool.not_true, Bool.false_or, decide_eq_true_eq] using proof h

theorem count_filter_cons (pattern : Pattern) (cell : Cell) (cells : List Cell) :
    ((cell :: cells).filter pattern).length =
      (if pattern cell then 1 else 0) + (cells.filter pattern).length := by
  cases h : pattern cell <;> simp [h, Nat.add_comm]

theorem sum_filter_cons (weight : Cell → Int) (pattern : Pattern) (cell : Cell) (cells : List Cell) :
    weightSum weight ((cell :: cells).filter pattern) =
      (if pattern cell then weight cell else 0) + weightSum weight (cells.filter pattern) := by
  cases h : pattern cell <;> simp [h, weightSum]

theorem min_cap_add (cap acc weight tail : Int) (positive : 0 ≤ tail) :
    min cap (min cap (acc + weight) + tail) = min cap (acc + (weight + tail)) := by
  simp only [Int.min_def]
  split <;> split <;> split <;> omega
theorem change_representative (support : List Cell) (p : Pattern) (source : Cell)
    (destination : Option Cell) (dummy : Cell) (outside : dummy ∉ support) :
    Agree support (change p source destination)
      (change p (if support.contains source then source else dummy)
        (destination.filter support.contains)) := by
  intro cell member
  have clearEq : (source = cell) ↔ ((if support.contains source then source else dummy) = cell) := by
    by_cases present : source ∈ support
    · simp [present]
    · have sourceNe : source ≠ cell := by intro same; exact present (same ▸ member)
      have dummyNe : dummy ≠ cell := by intro same; exact outside (same ▸ member)
      simp [present, sourceNe, dummyNe]
  have destinationEq : (destination = some cell) ↔ (destination.filter support.contains = some cell) := by
    cases destination with
    | none => rfl
    | some target =>
      by_cases present : target ∈ support
      · simp [Option.filter, present]
      · have targetNe : target ≠ cell := by intro same; exact present (same ▸ member)
        simp [Option.filter, present, targetNe]
  simp only [change, clearEq, destinationEq]
end NetHack.Sokoban.PatternCorrection
