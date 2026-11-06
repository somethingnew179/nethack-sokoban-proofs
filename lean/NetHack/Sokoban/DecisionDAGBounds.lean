/- Finite, checked interval metadata for the ordinary DAG evaluator.
Malformed rank edges still denote zero. Proposed bounds are never trusted. -/
import NetHack.Sokoban.DecisionDAGCountedCompact
namespace NetHack.Sokoban.DecisionDAGBounds
open DecisionDAG

structure Interval where
  lower : Int
  upper : Int
  deriving DecidableEq, Repr

def check (read : Nat → Node) (bounds : Nat → Interval) (root : Nat) : Bool :=
  match read root with
  | .literal value => decide ((bounds root).lower ≤ value ∧ value ≤ (bounds root).upper)
  | .branch _ low high =>
    if low < root ∧ high < root then decide
      ((bounds root).lower ≤ (bounds low).lower ∧
       (bounds root).lower ≤ (bounds high).lower ∧
       (bounds low).upper ≤ (bounds root).upper ∧
       (bounds high).upper ≤ (bounds root).upper)
    else decide ((bounds root).lower ≤ 0 ∧ 0 ≤ (bounds root).upper)

theorem checked_sound (read : Nat → Node) (bounds : Nat → Interval)
    (checked : ∀ root, check read bounds root = true) (p : Pattern) (root : Nat) :
    (bounds root).lower ≤ eval read p root ∧ eval read p root ≤ (bounds root).upper := by
  induction root using Nat.strongRecOn with
  | ind root ih =>
    have row := checked root
    cases code : read root with
    | literal value =>
      rw [eval_literal code p]
      simpa only [check, code, decide_eq_true_eq] using row
    | branch cell low high =>
      by_cases edges : low < root ∧ high < root
      · have limits : (bounds root).lower ≤ (bounds low).lower ∧
            (bounds root).lower ≤ (bounds high).lower ∧
            (bounds low).upper ≤ (bounds root).upper ∧
            (bounds high).upper ≤ (bounds root).upper := by
          simpa only [check, code, if_pos edges, decide_eq_true_eq] using row
        have lower := ih low edges.1
        have upper := ih high edges.2
        rw [eval_branch code edges p]
        cases p cell <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      · rw [eval, code]
        simp only [dif_neg edges]
        simpa only [check, code, if_neg edges, decide_eq_true_eq] using row

def inequalityCheck (bounds : Nat → Interval) (claim : DecisionDAGCountedCompact.Claim) : Bool :=
  decide ((bounds claim.left₁).upper + (bounds claim.left₂).upper ≤
    claim.slack + (bounds claim.right₁).lower + (bounds claim.right₂).lower)

theorem inequalityCheck_sound (read : Nat → Node) (bounds : Nat → Interval)
    (valid : ∀ root, check read bounds root = true)
    (claim : DecisionDAGCountedCompact.Claim)
    (checked : inequalityCheck bounds claim = true) :
    DecisionDAGCountedCompact.Holds read claim := by
  intro p _ _ _
  have a := checked_sound read bounds valid p claim.left₁
  have b := checked_sound read bounds valid p claim.left₂
  have c := checked_sound read bounds valid p claim.right₁
  have d := checked_sound read bounds valid p claim.right₂
  have numerical : (bounds claim.left₁).upper + (bounds claim.left₂).upper ≤
      claim.slack + (bounds claim.right₁).lower + (bounds claim.right₂).lower :=
    of_decide_eq_true checked
  omega

end NetHack.Sokoban.DecisionDAGBounds
