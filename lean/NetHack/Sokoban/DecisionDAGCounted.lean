/- Cardinality guards and short physical occupancy cubes for integer DAG
certificates. All rules have ordinary kernel soundness proofs. This permits
exact remaining-boulder budgets without a second Boolean guard circuit.
The module alone asserts no numerical bound for a NetHack map. -/
import NetHack.Sokoban.DecisionDAG

namespace NetHack.Sokoban.DecisionDAGCounted
open DecisionDAG

def count (cells : List Cell) (p : Pattern) : Int :=
  match cells with
  | [] => 0
  | cell :: cells => (if p cell then 1 else 0) + count cells p

theorem count_nonnegative (cells : List Cell) (p : Pattern) : 0 ≤ count cells p := by
  induction cells with
  | nil => simp [count]
  | cons cell cells ih => cases selected : p cell <;> simp only [count, selected, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem count_split (cells : List Cell) (p : Pattern) (cell : Cell) (bit : Bool)
    (selected : p cell = bit) :
    count (cells.filter (fun c => decide (c ≠ cell))) p = count cells p -
      (if bit then Int.ofNat ((cells.filter (fun c => decide (c = cell))).length) else 0) := by
  induction cells with
  | nil => simp [count]
  | cons head tail ih =>
    by_cases same : head = cell
    · subst head
      cases bit <;> simp_all [count] <;> omega
    · cases entry : p head <;> cases bit <;> simp_all [count] <;> omega

def Satisfies (bindings : List (Cell × Bool)) (p : Pattern) : Prop :=
  ∀ binding ∈ bindings, p binding.1 = binding.2

structure Claim where
  bindings : List (Cell × Bool)
  remaining : List Cell
  budget : Int
  left₁ : Nat
  left₂ : Nat
  right₁ : Nat
  right₂ : Nat
  slack : Int
  deriving DecidableEq, Repr

def Holds (read : Nat → Node) (claim : Claim) : Prop :=
  ∀ p, Satisfies claim.bindings p → count claim.remaining p ≤ claim.budget →
    eval read p claim.left₁ + eval read p claim.left₂ ≤
      claim.slack + eval read p claim.right₁ + eval read p claim.right₂

/-- Cancel identical diagram terms before sharing proof rows. Reference zero
need not denote zero: the replacement appears on both sides and cancels. -/
def Claim.normalize (claim : Claim) : Claim :=
  { claim with
    left₁ := if claim.left₁ = claim.right₁ then 0 else claim.left₁
    right₁ := if claim.left₁ = claim.right₁ then 0 else claim.right₁
    left₂ := if claim.left₂ = claim.right₂ then 0 else claim.left₂
    right₂ := if claim.left₂ = claim.right₂ then 0 else claim.right₂ }

theorem normalize_sound (read : Nat → Node) (claim : Claim)
    (valid : Holds read claim.normalize) : Holds read claim := by
  intro p bindings budget
  have h := valid p bindings budget
  by_cases first : claim.left₁ = claim.right₁ <;>
    by_cases second : claim.left₂ = claim.right₂ <;>
    simp only [Claim.normalize, first, second, ↓reduceIte] at h
  · rw [first, second]
    omega
  · rw [first]
    omega
  · rw [second]
    omega
  · exact h

def Claim.cofactor (claim : Claim) (read : Nat → Node) (cell : Cell) (bit : Bool) : Claim where
  bindings := claim.bindings.filter (fun binding => decide (binding.1 ≠ cell))
  remaining := claim.remaining.filter (fun c => decide (c ≠ cell))
  budget := claim.budget -
    (if bit then Int.ofNat ((claim.remaining.filter (fun c => decide (c = cell))).length) else 0)
  left₁ := splitRef read cell bit claim.left₁
  left₂ := splitRef read cell bit claim.left₂
  right₁ := splitRef read cell bit claim.right₁
  right₂ := splitRef read cell bit claim.right₂
  slack := claim.slack

theorem cofactor_sound (read : Nat → Node) (claim : Claim) (cell : Cell) (bit : Bool)
    (valid : Holds read (claim.cofactor read cell bit)) (p : Pattern)
    (selected : p cell = bit) (bindings : Satisfies claim.bindings p)
    (budget : count claim.remaining p ≤ claim.budget) :
    eval read p claim.left₁ + eval read p claim.left₂ ≤
      claim.slack + eval read p claim.right₁ + eval read p claim.right₂ := by
  have nextBindings : Satisfies (claim.cofactor read cell bit).bindings p := by
    intro binding member
    exact bindings binding (List.mem_filter.mp member).1
  have nextBudget : count (claim.cofactor read cell bit).remaining p ≤
      (claim.cofactor read cell bit).budget := by
    simp only [Claim.cofactor, count_split _ p cell bit selected]
    omega
  have h := valid p nextBindings nextBudget
  simpa only [Claim.cofactor, eval_splitRef read cell bit _ p selected] using h

theorem split_sound (read : Nat → Node) (claim : Claim) (cell : Cell)
    (low : Holds read (claim.cofactor read cell false))
    (high : Holds read (claim.cofactor read cell true)) : Holds read claim := by
  intro p bindings budget
  cases selected : p cell with
  | false => exact cofactor_sound read claim cell false low p selected bindings budget
  | true => exact cofactor_sound read claim cell true high p selected bindings budget

theorem assume_sound (read : Nat → Node) (claim : Claim) (cell : Cell) (bit : Bool)
    (member : (cell, bit) ∈ claim.bindings)
    (valid : Holds read (claim.cofactor read cell bit)) : Holds read claim := by
  intro p bindings budget
  exact cofactor_sound read claim cell bit valid p (bindings (cell, bit) member) bindings budget

def leafCheck (read : Nat → Node) (claim : Claim) : Bool :=
  if claim.budget < 0 then true else
    match read claim.left₁, read claim.left₂, read claim.right₁, read claim.right₂ with
    | .literal a, .literal b, .literal c, .literal d => decide (a + b ≤ claim.slack + c + d)
    | _, _, _, _ => false

theorem leafCheck_sound (read : Nat → Node) (claim : Claim)
    (checked : leafCheck read claim = true) : Holds read claim := by
  intro p _ budget
  by_cases impossible : claim.budget < 0
  · have nonnegative := count_nonnegative claim.remaining p
    omega
  · simp only [leafCheck, if_neg impossible] at checked
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
  | assume (cell : Cell) (bit : Bool) (child : Nat)
  deriving DecidableEq, Repr

structure Row where
  claim : Claim
  rule : Rule
  deriving DecidableEq, Repr

def checkRow (read : Nat → Node) (rows : Nat → Row) (index : Nat) : Bool :=
  match (rows index).rule with
  | .leaf => leafCheck read (rows index).claim
  | .split cell low high => decide (low < index ∧ high < index ∧
    (rows low).claim = ((rows index).claim.cofactor read cell false).normalize ∧
    (rows high).claim = ((rows index).claim.cofactor read cell true).normalize)
  | .assume cell bit child => decide (child < index ∧ (cell, bit) ∈ (rows index).claim.bindings ∧
    (rows child).claim = ((rows index).claim.cofactor read cell bit).normalize)

theorem checked_sound (read : Nat → Node) (rows : Nat → Row) (count : Nat)
    (checked : ∀ index, index < count → checkRow read rows index = true)
    (index : Nat) (inside : index < count) : Holds read (rows index).claim := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
    have row := checked index inside
    cases rule : (rows index).rule with
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

end NetHack.Sokoban.DecisionDAGCounted
