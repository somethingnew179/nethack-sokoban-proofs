/- A small proof checker for guarded integer decision diagrams.
The reader and proof rows are untrusted data. Soundness quantifies over every
Boolean assignment. No evaluator outside Lean and no reachability assumption
is used. Invalid diagram edges denote zero; they cannot introduce an axiom.
This module alone asserts no bound for any puzzle. -/
import NetHack.Sokoban.PatternCorrection

namespace NetHack.Sokoban.DecisionDAG
abbrev Pattern := Cell → Bool

inductive Node where
  | literal (value : Int)
  | branch (cell low high : Nat)
  deriving DecidableEq, Repr

def eval (read : Nat → Node) (p : Pattern) (root : Nat) : Int :=
  match read root with
  | .literal value => value
  | .branch cell low high =>
    if _edges : low < root ∧ high < root then
      if p cell then eval read p high else eval read p low
    else 0
termination_by root

theorem eval_literal {read : Nat → Node} {root : Nat} {value : Int}
    (code : read root = .literal value) (p : Pattern) : eval read p root = value := by
  rw [eval, code]

theorem eval_branch {read : Nat → Node} {root cell low high : Nat}
    (code : read root = .branch cell low high) (edges : low < root ∧ high < root)
    (p : Pattern) : eval read p root = if p cell then eval read p high else eval read p low := by
  rw [eval, code]
  simp only [dif_pos edges]

def splitRef (read : Nat → Node) (cell : Cell) (bit : Bool) (root : Nat) : Nat :=
  match read root with
  | .literal _ => root
  | .branch testCell low high =>
    if testCell = cell ∧ low < root ∧ high < root then
      if bit then high else low
    else root

theorem eval_splitRef (read : Nat → Node) (cell : Cell) (bit : Bool)
    (root : Nat) (p : Pattern) (selected : p cell = bit) :
    eval read p (splitRef read cell bit root) = eval read p root := by
  unfold splitRef
  cases code : read root with
  | literal value => rfl
  | branch testCell low high =>
    by_cases valid : testCell = cell ∧ low < root ∧ high < root
    · simp only [if_pos valid]
      rw [eval_branch code valid.2]
      rw [valid.1, selected]
      cases bit <;> rfl
    · simp only [if_neg valid]

structure Claim where
  guard : Nat
  left₁ : Nat
  left₂ : Nat
  right₁ : Nat
  right₂ : Nat
  slack : Int
  deriving DecidableEq, Repr

def Holds (read : Nat → Node) (claim : Claim) : Prop :=
  ∀ p, eval read p claim.guard = 1 →
    eval read p claim.left₁ + eval read p claim.left₂ ≤
      claim.slack + eval read p claim.right₁ + eval read p claim.right₂

def Claim.split (claim : Claim) (read : Nat → Node) (cell : Cell) (bit : Bool) : Claim where
  guard := splitRef read cell bit claim.guard
  left₁ := splitRef read cell bit claim.left₁
  left₂ := splitRef read cell bit claim.left₂
  right₁ := splitRef read cell bit claim.right₁
  right₂ := splitRef read cell bit claim.right₂
  slack := claim.slack

theorem split_sound (read : Nat → Node) (claim : Claim) (cell : Cell)
    (low : Holds read (claim.split read cell false))
    (high : Holds read (claim.split read cell true)) : Holds read claim := by
  intro p guard
  have transfer (bit : Bool) (selected : p cell = bit)
      (valid : Holds read (claim.split read cell bit)) :
      eval read p claim.left₁ + eval read p claim.left₂ ≤
        claim.slack + eval read p claim.right₁ + eval read p claim.right₂ := by
    have h := valid p
    simp only [Claim.split, eval_splitRef read cell bit _ p selected] at h
    exact h guard
  cases selected : p cell with
  | false => exact transfer false selected low
  | true => exact transfer true selected high

def leafCheck (read : Nat → Node) (claim : Claim) : Bool :=
  match read claim.guard with
  | .literal value =>
    if value ≠ 1 then true else
      match read claim.left₁, read claim.left₂, read claim.right₁, read claim.right₂ with
      | .literal a, .literal b, .literal c, .literal d => decide (a + b ≤ claim.slack + c + d)
      | _, _, _, _ => false
  | _ => false

theorem leafCheck_sound (read : Nat → Node) (claim : Claim)
    (checked : leafCheck read claim = true) : Holds read claim := by
  intro p guard
  cases hg : read claim.guard with
  | branch _ _ _ => simp [leafCheck, hg] at checked
  | literal value =>
    have valueOne : value = 1 := by rw [eval_literal hg p] at guard; exact guard
    simp only [leafCheck, hg, valueOne, ne_eq, not_true_eq_false, ↓reduceIte] at checked
    cases ha : read claim.left₁ <;> cases hb : read claim.left₂ <;>
      cases hc : read claim.right₁ <;> cases hd : read claim.right₂ <;>
      simp only [ha, hb, hc, hd, Bool.false_eq_true] at checked
    all_goals first
      | contradiction
      | simpa only [eval_literal ha p, eval_literal hb p, eval_literal hc p,
          eval_literal hd p, decide_eq_true_eq] using checked

inductive Rule where
  | leaf
  | split (cell low high : Nat)
  deriving DecidableEq, Repr

structure Row where
  claim : Claim
  rule : Rule
  deriving DecidableEq, Repr

def checkRow (read : Nat → Node) (rows : Nat → Row) (index : Nat) : Bool :=
  match (rows index).rule with
  | .leaf => leafCheck read (rows index).claim
  | .split cell low high =>
    decide (low < index ∧ high < index ∧
      (rows low).claim = (rows index).claim.split read cell false ∧
      (rows high).claim = (rows index).claim.split read cell true)

/- Each row is checked only once. In particular, importing a row index never
silently trusts its conclusion. Strong induction supplies both parent proofs. -/
theorem checked_sound (read : Nat → Node) (rows : Nat → Row) (count : Nat)
    (checked : ∀ index, index < count → checkRow read rows index = true)
    (index : Nat) (inside : index < count) : Holds read (rows index).claim := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
    have row := checked index inside
    cases rule : (rows index).rule with
    | leaf =>
      exact leafCheck_sound read _ (by simpa only [checkRow, rule] using row)
    | split cell low high =>
      have children : low < index ∧ high < index ∧
          (rows low).claim = (rows index).claim.split read cell false ∧
          (rows high).claim = (rows index).claim.split read cell true := by
        simpa only [checkRow, rule, decide_eq_true_eq] using row
      apply split_sound read _ cell
      · rw [← children.2.2.1]
        exact ih low children.1 (Nat.lt_trans children.1 inside)
      · rw [← children.2.2.2]
        exact ih high children.2.1 (Nat.lt_trans children.2.1 inside)

end NetHack.Sokoban.DecisionDAG
