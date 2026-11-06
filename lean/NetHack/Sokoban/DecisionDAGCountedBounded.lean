/- The counted/cube checker with an additional verified interval leaf rule.
All prior cofactor, count, normalization and weakening premises are preserved.
This interface alone is not a concrete numerical certificate. -/
import NetHack.Sokoban.DecisionDAGBounds
namespace NetHack.Sokoban.DecisionDAGCountedBounded
open DecisionDAG (Pattern Node eval)
open DecisionDAGCountedCompact
inductive Rule where
  | bounds
  | leaf
  | split (cell low high : Nat)
  | assume (cell : Cell) (bit : Bool) (child : Nat)
  | weaken (child : Nat)
  deriving DecidableEq, Repr

structure Row where
  claim : Claim
  rule : Rule
  deriving DecidableEq, Repr

def checkRow (read : Nat → Node) (bounds : Nat → DecisionDAGBounds.Interval) (rows : Nat → Row) (index : Nat) : Bool :=
  match (rows index).rule with
  | .bounds => DecisionDAGBounds.inequalityCheck bounds (rows index).claim
  | .leaf => leafCheck read (rows index).claim
  | .split cell low high => decide (low < index ∧ high < index ∧
    (rows low).claim = ((rows index).claim.cofactor read cell false).normalize ∧
    (rows high).claim = ((rows index).claim.cofactor read cell true).normalize)
  | .assume cell bit child => decide (child < index ∧ (cell, bit) ∈ (rows index).claim.bindings ∧
    (rows child).claim = ((rows index).claim.cofactor read cell bit).normalize)
  | .weaken child => decide (child < index ∧
    (rows child).claim.remaining.Sublist (rows index).claim.remaining ∧
    (rows child).claim = ({(rows index).claim with remaining := (rows child).claim.remaining}).normalize)

theorem checked_sound (read : Nat → Node) (bounds : Nat → DecisionDAGBounds.Interval)
    (valid : ∀ root, DecisionDAGBounds.check read bounds root = true) (rows : Nat → Row) (count : Nat)
    (checked : ∀ index, index < count → checkRow read bounds rows index = true)
    (index : Nat) (inside : index < count) : Holds read (rows index).claim := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
    have row := checked index inside
    cases rule : (rows index).rule with
    | bounds =>
      exact DecisionDAGBounds.inequalityCheck_sound read bounds valid _
        (by simpa only [checkRow, rule] using row)
    | leaf => exact leafCheck_sound read _ (by simpa only [checkRow, rule] using row)
    | split cell low high =>
      have children : low < index ∧ high < index ∧
          (rows low).claim = ((rows index).claim.cofactor read cell false).normalize ∧
          (rows high).claim = ((rows index).claim.cofactor read cell true).normalize := by
        simpa only [checkRow, rule, decide_eq_true_eq] using row
      apply split_sound read _ cell
      · apply normalize_sound
        rw [← children.2.2.1]
        exact ih low children.1 (Nat.lt_trans children.1 inside)
      · apply normalize_sound
        rw [← children.2.2.2]
        exact ih high children.2.1 (Nat.lt_trans children.2.1 inside)
    | assume cell bit child =>
      have childData : child < index ∧ (cell, bit) ∈ (rows index).claim.bindings ∧
          (rows child).claim = ((rows index).claim.cofactor read cell bit).normalize := by
        simpa only [checkRow, rule, decide_eq_true_eq] using row
      apply assume_sound read _ cell bit childData.2.1
      apply normalize_sound
      rw [← childData.2.2]
      exact ih child childData.1 (Nat.lt_trans childData.1 inside)
    | weaken child =>
      have childData : child < index ∧
          (rows child).claim.remaining.Sublist (rows index).claim.remaining ∧
          (rows child).claim = ({(rows index).claim with remaining := (rows child).claim.remaining}).normalize := by
        simpa only [checkRow, rule, decide_eq_true_eq] using row
      apply weaken_sound read _ (rows child).claim.remaining childData.2.1
      apply normalize_sound
      rw [← childData.2.2]
      exact ih child childData.1 (Nat.lt_trans childData.1 inside)

end NetHack.Sokoban.DecisionDAGCountedBounded
