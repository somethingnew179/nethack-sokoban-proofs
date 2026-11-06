/- Compact cardinality guards and short physical occupancy cubes for integer DAG
certificates. All rules have ordinary kernel soundness proofs. This permits
exact remaining-boulder budgets without a second Boolean guard circuit.
The module alone asserts no numerical bound for a NetHack map. -/
import NetHack.Sokoban.DecisionDAG

namespace NetHack.Sokoban.DecisionDAGCountedCompact
open DecisionDAG

def count (cells : List Cell) (p : Pattern) : Int :=
  match cells with
  | [] => 0
  | cell :: cells => (if p cell then 1 else 0) + count cells p

theorem count_nonnegative (cells : List Cell) (p : Pattern) : 0 ≤ count cells p := by
  induction cells with
  | nil => simp [count]
  | cons cell cells ih => cases selected : p cell <;> simp only [count, selected, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem count_le_length (cells : List Cell) (p : Pattern) : count cells p ≤ Int.ofNat cells.length := by
  induction cells with
  | nil => simp [count]
  | cons cell cells ih =>
    cases selected : p cell <;> simp only [Int.ofNat_eq_natCast] at ih ⊢ <;>
      simp [count, selected] <;> omega

theorem count_sublist {small large : List Cell} (sub : small.Sublist large) (p : Pattern) :
    count small p ≤ count large p := by
  induction sub with
  | slnil => simp [count]
  | cons head sub ih => cases selected : p head <;> simp [count, selected] <;> omega
  | cons_cons head sub ih => cases selected : p head <;> simp [count, selected] <;> omega

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
  decreasingOnly : Bool := false
  deriving DecidableEq, Repr

def Trigger (read : Nat → Node) (claim : Claim) (p : Pattern) : Prop :=
  claim.decreasingOnly = true → eval read p claim.right₂ < eval read p claim.left₂

def Holds (read : Nat → Node) (claim : Claim) : Prop :=
  ∀ p, Satisfies claim.bindings p → count claim.remaining p ≤ claim.budget →
    Trigger read claim p →
    eval read p claim.left₁ + eval read p claim.left₂ ≤
      claim.slack + eval read p claim.right₁ + eval read p claim.right₂

/-- Cancel identical diagram terms before sharing proof rows. Reference zero
need not denote zero: the replacement appears on both sides and cancels. -/
def Claim.normalize (claim : Claim) : Claim :=
  { claim with
    budget := min claim.budget (Int.ofNat claim.remaining.length)
    left₁ := if claim.left₁ = claim.right₁ then 0 else claim.left₁
    right₁ := if claim.left₁ = claim.right₁ then 0 else claim.right₁
    left₂ := if claim.left₂ = claim.right₂ then 0 else claim.left₂
    right₂ := if claim.left₂ = claim.right₂ then 0 else claim.right₂ }

theorem normalize_sound (read : Nat → Node) (claim : Claim)
    (valid : Holds read claim.normalize) : Holds read claim := by
  intro p bindings budget trigger
  have size := count_le_length claim.remaining p
  have capped : count claim.remaining p ≤ min claim.budget (Int.ofNat claim.remaining.length) := by omega
  have nextTrigger : Trigger read claim.normalize p := by
    intro mode
    have original := trigger mode
    by_cases second : claim.left₂ = claim.right₂
    · rw [second] at original
      omega
    · simpa only [Claim.normalize, if_neg second] using original
  have h := valid p bindings capped nextTrigger
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

theorem weaken_sound (read : Nat → Node) (claim : Claim) (small : List Cell)
    (sub : small.Sublist claim.remaining)
    (valid : Holds read {claim with remaining := small}) : Holds read claim := by
  intro p bindings budget trigger
  exact valid p bindings (Int.le_trans (count_sublist sub p) budget) trigger

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
  decreasingOnly := claim.decreasingOnly

theorem cofactor_sound (read : Nat → Node) (claim : Claim) (cell : Cell) (bit : Bool)
    (valid : Holds read (claim.cofactor read cell bit)) (p : Pattern)
    (selected : p cell = bit) (bindings : Satisfies claim.bindings p)
    (budget : count claim.remaining p ≤ claim.budget) (trigger : Trigger read claim p) :
    eval read p claim.left₁ + eval read p claim.left₂ ≤
      claim.slack + eval read p claim.right₁ + eval read p claim.right₂ := by
  have nextBindings : Satisfies (claim.cofactor read cell bit).bindings p := by
    intro binding member
    exact bindings binding (List.mem_filter.mp member).1
  have nextBudget : count (claim.cofactor read cell bit).remaining p ≤
      (claim.cofactor read cell bit).budget := by
    simp only [Claim.cofactor, count_split _ p cell bit selected]
    omega
  have nextTrigger : Trigger read (claim.cofactor read cell bit) p := by
    intro mode
    have original := trigger mode
    simpa only [Claim.cofactor, eval_splitRef read cell bit _ p selected] using original
  have h := valid p nextBindings nextBudget nextTrigger
  simpa only [Claim.cofactor, eval_splitRef read cell bit _ p selected] using h

theorem split_sound (read : Nat → Node) (claim : Claim) (cell : Cell)
    (low : Holds read (claim.cofactor read cell false))
    (high : Holds read (claim.cofactor read cell true)) : Holds read claim := by
  intro p bindings budget trigger
  cases selected : p cell with
  | false => exact cofactor_sound read claim cell false low p selected bindings budget trigger
  | true => exact cofactor_sound read claim cell true high p selected bindings budget trigger

theorem assume_sound (read : Nat → Node) (claim : Claim) (cell : Cell) (bit : Bool)
    (member : (cell, bit) ∈ claim.bindings)
    (valid : Holds read (claim.cofactor read cell bit)) : Holds read claim := by
  intro p bindings budget trigger
  exact cofactor_sound read claim cell bit valid p (bindings (cell, bit) member) bindings budget trigger

def skipCheck (read : Nat → Node) (claim : Claim) : Bool :=
  claim.decreasingOnly &&
    (if claim.left₂ = claim.right₂ then true else
      match read claim.left₂, read claim.right₂ with
      | .literal a, .literal b => decide (a ≤ b)
      | _, _ => false)

theorem skipCheck_sound (read : Nat → Node) (claim : Claim)
    (checked : skipCheck read claim = true) (p : Pattern) : ¬Trigger read claim p := by
  intro trigger
  have data := Bool.and_eq_true_iff.mp checked
  have less := trigger data.1
  by_cases same : claim.left₂ = claim.right₂
  · rw [same] at less
    omega
  · have body := data.2
    simp only [if_neg same] at body
    cases left : read claim.left₂ <;> cases right : read claim.right₂ <;>
      simp only [left, right, Bool.false_eq_true, decide_eq_true_eq] at body
    all_goals first
      | contradiction
      | (rw [eval_literal left p, eval_literal right p] at less; omega)

def leafCheck (read : Nat → Node) (claim : Claim) : Bool :=
  if skipCheck read claim then true else if claim.budget < 0 then true else
    match read claim.left₁, read claim.left₂, read claim.right₁, read claim.right₂ with
    | .literal a, .literal b, .literal c, .literal d => decide (a + b ≤ claim.slack + c + d)
    | _, _, _, _ => false

theorem leafCheck_sound (read : Nat → Node) (claim : Claim)
    (checked : leafCheck read claim = true) : Holds read claim := by
  intro p _ budget trigger
  by_cases skip : skipCheck read claim = true
  · exact False.elim (skipCheck_sound read claim skip p trigger)
  · simp only [leafCheck, if_neg skip] at checked
    by_cases impossible : claim.budget < 0
    · have nonnegative := count_nonnegative claim.remaining p
      omega
    · simp only [if_neg impossible] at checked
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
  | weaken (child : Nat)
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
  | .weaken child => decide (child < index ∧
    (rows child).claim.remaining.Sublist (rows index).claim.remaining ∧
    (rows child).claim = ({(rows index).claim with remaining := (rows child).claim.remaining}).normalize)

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
    | weaken child =>
      have childData : child < index ∧
          (rows child).claim.remaining.Sublist (rows index).claim.remaining ∧
          (rows child).claim = ({(rows index).claim with remaining := (rows child).claim.remaining}).normalize := by
        simpa only [checkRow, rule, decide_eq_true_eq] using row
      apply weaken_sound read _ (rows child).claim.remaining childData.2.1
      apply normalize_sound
      rw [← childData.2.2]
      exact ih child childData.1 (Nat.lt_trans childData.1 inside)

end NetHack.Sokoban.DecisionDAGCountedCompact
