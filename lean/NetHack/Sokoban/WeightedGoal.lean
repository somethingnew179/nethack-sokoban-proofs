/- Counted weighted terminal certificates for the original puzzle potential.
The checker proves beta+gamma is paid by remaining negative crate weights.
No concrete map bound or goal certificate is assumed in this generic file. -/
import NetHack.Sokoban.DecisionDAGBounds
set_option linter.unusedSimpArgs false
namespace NetHack.Sokoban.WeightedGoal
open DecisionDAG (Node Pattern eval splitRef eval_splitRef)
open DecisionDAGCountedCompact (count count_split count_nonnegative count_le_length count_sublist)

def sum (weight : Cell → Int) : List Cell → Pattern → Int
  | [], _ => 0
  | cell :: tail, p => (if p cell then weight cell else 0) + sum weight tail p

def occurrences (weight : Cell → Int) : List Cell → Cell → Int
  | [], _ => 0
  | head :: tail, cell => (if head = cell then weight cell else 0) + occurrences weight tail cell

theorem sum_eq_weightSum (weight : Cell → Int) (cells : List Cell) (p : Pattern) :
    sum weight cells p = LowerBounds.weightSum weight (cells.filter p) := by
  induction cells with
  | nil => rfl
  | cons cell tail ih => cases selected : p cell <;> simp [sum, LowerBounds.weightSum, selected, ih]

theorem sum_nonnegative (weight : Cell → Int) (positive : ∀ cell, 0 ≤ weight cell)
    (cells : List Cell) (p : Pattern) : 0 ≤ sum weight cells p := by
  induction cells with
  | nil => exact Int.le_refl _
  | cons cell tail ih => cases p cell <;> simp only [sum, Bool.false_eq_true, ↓reduceIte] <;> have := positive cell <;> omega

theorem sum_sublist (weight : Cell → Int) (positive : ∀ cell, 0 ≤ weight cell)
    {small large : List Cell} (sub : small.Sublist large) (p : Pattern) :
    sum weight small p ≤ sum weight large p := by
  induction sub with
  | slnil => simp [sum]
  | cons head sub ih => cases p head <;> simp only [sum, Bool.false_eq_true, ↓reduceIte] <;> have := positive head <;> omega
  | cons_cons head sub ih => simp only [sum]; omega

theorem sum_split (weight : Cell → Int) (cells : List Cell) (p : Pattern)
    (cell : Cell) (bit : Bool) (selected : p cell = bit) :
    sum weight (cells.filter (fun c => decide (c ≠ cell))) p +
      (if bit then occurrences weight cells cell else 0) = sum weight cells p := by
  induction cells with
  | nil => simp [sum, occurrences]
  | cons head tail ih =>
    by_cases same : head = cell
    · subst head
      cases bit <;> simp_all [sum, occurrences] <;> omega
    · cases entry : p head <;> cases bit <;> simp_all [sum, occurrences] <;> omega

structure Claim where
  remaining : List Cell
  budget : Int
  beta : Nat
  gamma : Nat
  debt : Int
  deriving DecidableEq, Repr

def Holds (read : Nat → Node) (weight : Cell → Int) (claim : Claim) : Prop :=
  ∀ p, count claim.remaining p ≤ claim.budget →
    eval read p claim.beta + eval read p claim.gamma ≤ claim.debt + sum weight claim.remaining p

def Claim.normalize (claim : Claim) : Claim :=
  {claim with budget := min claim.budget (Int.ofNat claim.remaining.length)}

theorem normalize_sound (read : Nat → Node) (weight : Cell → Int) (claim : Claim)
    (valid : Holds read weight claim.normalize) : Holds read weight claim := by
  intro p budget
  apply valid p
  have size := count_le_length claim.remaining p
  change count claim.remaining p ≤ min claim.budget (Int.ofNat claim.remaining.length)
  omega

def Claim.cofactor (claim : Claim) (read : Nat → Node) (weight : Cell → Int)
    (cell : Cell) (bit : Bool) : Claim where
  remaining := claim.remaining.filter (fun c => decide (c ≠ cell))
  budget := claim.budget - (if bit then Int.ofNat ((claim.remaining.filter (fun c => decide (c = cell))).length) else 0)
  beta := splitRef read cell bit claim.beta
  gamma := splitRef read cell bit claim.gamma
  debt := claim.debt + (if bit then occurrences weight claim.remaining cell else 0)

theorem cofactor_sound (read : Nat → Node) (weight : Cell → Int) (claim : Claim)
    (cell : Cell) (bit : Bool) (valid : Holds read weight (claim.cofactor read weight cell bit))
    (p : Pattern) (selected : p cell = bit) (budget : count claim.remaining p ≤ claim.budget) :
    eval read p claim.beta + eval read p claim.gamma ≤ claim.debt + sum weight claim.remaining p := by
  have nextBudget : count (claim.cofactor read weight cell bit).remaining p ≤
      (claim.cofactor read weight cell bit).budget := by
    simp only [Claim.cofactor, count_split _ p cell bit selected]
    omega
  have result := valid p nextBudget
  simp only [Claim.cofactor, eval_splitRef read cell bit _ p selected] at result
  have totals := sum_split weight claim.remaining p cell bit selected
  omega

def leafCheck (bounds : Nat → DecisionDAGBounds.Interval) (claim : Claim) : Bool :=
  decide (claim.budget < 0 ∨ (bounds claim.beta).upper + (bounds claim.gamma).upper ≤ claim.debt)

theorem leaf_sound (read : Nat → Node) (bounds : Nat → DecisionDAGBounds.Interval)
    (validBounds : ∀ root, DecisionDAGBounds.check read bounds root = true)
    (weight : Cell → Int) (positive : ∀ cell, 0 ≤ weight cell) (claim : Claim)
    (checked : leafCheck bounds claim = true) : Holds read weight claim := by
  intro p budget
  have alternatives : claim.budget < 0 ∨
      (bounds claim.beta).upper + (bounds claim.gamma).upper ≤ claim.debt := of_decide_eq_true checked
  rcases alternatives with impossible | bounded
  · have := count_nonnegative claim.remaining p
    omega
  · have beta := DecisionDAGBounds.checked_sound read bounds validBounds p claim.beta
    have gamma := DecisionDAGBounds.checked_sound read bounds validBounds p claim.gamma
    have paid := sum_nonnegative weight positive claim.remaining p
    omega

inductive Rule where
  | leaf
  | split (cell low high : Nat)
  | weaken (child : Nat)
  deriving DecidableEq, Repr
structure Row where
  claim : Claim
  rule : Rule
  deriving DecidableEq, Repr

def checkRow (read : Nat → Node) (bounds : Nat → DecisionDAGBounds.Interval)
    (weight : Cell → Int) (rows : Nat → Row) (index : Nat) : Bool :=
  match (rows index).rule with
  | .leaf => leafCheck bounds (rows index).claim
  | .split cell low high => decide (low < index ∧ high < index ∧
      (rows low).claim = ((rows index).claim.cofactor read weight cell false).normalize ∧
      (rows high).claim = ((rows index).claim.cofactor read weight cell true).normalize)
  | .weaken child => decide (child < index ∧
      (rows child).claim.remaining.Sublist (rows index).claim.remaining ∧
      (rows child).claim = ({(rows index).claim with remaining := (rows child).claim.remaining}).normalize)

theorem checked_sound (read : Nat → Node) (bounds : Nat → DecisionDAGBounds.Interval)
    (validBounds : ∀ root, DecisionDAGBounds.check read bounds root = true)
    (weight : Cell → Int) (positive : ∀ cell, 0 ≤ weight cell) (rows : Nat → Row) (rowCount : Nat)
    (checked : ∀ index, index < rowCount → checkRow read bounds weight rows index = true)
    (index : Nat) (inside : index < rowCount) : Holds read weight (rows index).claim := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
    have row := checked index inside
    cases rule : (rows index).rule with
    | leaf =>
      exact leaf_sound read bounds validBounds weight positive _
        (by simpa only [checkRow, rule] using row)
    | split cell low high =>
      have facts : low < index ∧ high < index ∧
          (rows low).claim = ((rows index).claim.cofactor read weight cell false).normalize ∧
          (rows high).claim = ((rows index).claim.cofactor read weight cell true).normalize := by
        simpa only [checkRow, rule, decide_eq_true_eq] using row
      intro p budget
      cases selected : p cell with
      | false =>
        apply cofactor_sound read weight _ cell false _ p selected budget
        apply normalize_sound
        rw [← facts.2.2.1]
        exact ih low facts.1 (Nat.lt_trans facts.1 inside)
      | true =>
        apply cofactor_sound read weight _ cell true _ p selected budget
        apply normalize_sound
        rw [← facts.2.2.2]
        exact ih high facts.2.1 (Nat.lt_trans facts.2.1 inside)
    | weaken child =>
      have facts : child < index ∧ (rows child).claim.remaining.Sublist (rows index).claim.remaining ∧
          (rows child).claim = ({(rows index).claim with remaining := (rows child).claim.remaining}).normalize := by
        simpa only [checkRow, rule, decide_eq_true_eq] using row
      have childProof := ih child facts.1 (Nat.lt_trans facts.1 inside)
      rw [facts.2.2] at childProof
      have next := normalize_sound read weight _ childProof
      intro p budget
      have amount := count_sublist facts.2.1 p
      have cost := sum_sublist weight positive facts.2.1 p
      have result := next p (by
        change count (rows child).claim.remaining p ≤ (rows index).claim.budget
        omega)
      change eval read p (rows index).claim.beta + eval read p (rows index).claim.gamma ≤
        (rows index).claim.debt + sum weight (rows child).claim.remaining p at result
      omega

end NetHack.Sokoban.WeightedGoal
