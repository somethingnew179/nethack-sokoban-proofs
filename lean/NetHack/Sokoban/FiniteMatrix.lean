/- Explicit intermediate values for finite residual row certificates.
Every proposed edge is checked against the unchanged Model.step, every
direction is covered, and positive hero cells are covered independently.
A zero bonus needs no lookup: every residual bonus is a Nat and hence
nonnegative. Positive bonuses require the exact lookup equality.
Literal query/value witnesses avoid composing a large lookup with a partially
reduced transition. They are not trusted: all equalities and inequalities are
ordinary decidable propositions, with soundness proved below. -/
import NetHack.Sokoban.FiniteResidual

namespace NetHack.Sokoban.FiniteMatrix
open LowerBounds FiniteResidual

structure PushWitness where
  canonical : State := default
  query : Nat := 0
  before : Int := 0
  after : Int := 0
  bonus : Nat := 0

structure Edge where
  direction : Dir
  expected : Option Transition
  witness : PushWitness := {}

structure HeroRow where
  hero : Cell
  edges : List Edge

def pushCheck (base : State → Int) (normalize : State → State)
    (key : State → Nat) (evaluate : State → Nat → Nat)
    (entry : Entry) (hero : Cell) (t : Transition) (w : PushWitness) : Bool :=
  decide (base (entry.at hero) = w.before ∧ base t.state = w.after ∧
    (w.bonus = 0 ∨ (normalize t.state = w.canonical ∧ key w.canonical = w.query ∧
      evaluate w.canonical w.query = w.bonus)) ∧
    w.before + Int.ofNat (entry.score hero) ≤
      Int.ofNat t.pushCost + w.after + Int.ofNat w.bonus)

def edgeCheck (board : Board) (base : State → Int) (normalize : State → State)
    (key : State → Nat) (evaluate : State → Nat → Nat)
    (entry : Entry) (hero : Cell) (edge : Edge) : Bool :=
  decide (step board (entry.at hero) edge.direction = edge.expected) &&
    match edge.expected with
    | none => true
    | some t => if t.pushed then pushCheck base normalize key evaluate entry hero t edge.witness
        else decide (entry.score hero ≤ entry.score t.state.player)

def directionsCovered (edges : List Edge) : Bool :=
  allDirs.all fun d => edges.any fun edge => decide (edge.direction = d)

def rowCheck (board : Board) (base : State → Int) (normalize : State → State)
    (key : State → Nat) (evaluate : State → Nat → Nat) (entry : Entry) (row : HeroRow) : Bool :=
  directionsCovered row.edges && row.edges.all (edgeCheck board base normalize key evaluate entry row.hero)

def coverage (entry : Entry) (heroes : List Cell) (rows : List HeroRow) : Bool :=
  heroes.all fun hero => decide (entry.score hero = 0) || rows.any fun row => decide (row.hero = hero)

def check (board : Board) (base : State → Int) (normalize : State → State)
    (key : State → Nat) (evaluate : State → Nat → Nat)
    (entry : Entry) (heroes : List Cell) (rows : List HeroRow) : Bool :=
  coverage entry heroes rows && rows.all (rowCheck board base normalize key evaluate entry)

theorem pushCheck_sound (base : State → Int) (normalize : State → State)
    (key : State → Nat) (evaluate : State → Nat → Nat)
    (entry : Entry) (hero : Cell) (t : Transition) (w : PushWitness)
    (checked : pushCheck base normalize key evaluate entry hero t w = true) :
    base (entry.at hero) + Int.ofNat (entry.score hero) ≤
      Int.ofNat t.pushCost + base t.state + Int.ofNat (evaluate (normalize t.state) (key (normalize t.state))) := by
  have facts := of_decide_eq_true checked
  rcases facts with ⟨before, after, extra, numeric⟩
  rcases extra with zero | precise
  · rw [before, after]
    rw [zero] at numeric
    simp only [Int.ofNat_eq_natCast] at numeric ⊢
    omega
  · rcases precise with ⟨canonical, query, bonus⟩
    rw [before, after, canonical, query, bonus]
    exact numeric

theorem edgeCheck_sound (board : Board) (base : State → Int)
    (normalizer : Normalizer board) (normalize : State → State)
    (table : Table) (key : State → Nat) (evaluate : State → Nat → Nat)
    (entry : Entry) (hero : Cell) (edge : Edge)
    (valid : StepBound board base)
    (normalizerEq : ∀ s, normalizer.normalize s = normalize s)
    (evaluateEq : ∀ s, evaluate s (key s) = rawBonus table key s)
    (honest : ∀ p, rawBonus table key (normalizer.normalize (entry.at p)) = entry.score p)
    (checked : edgeCheck board base normalize key evaluate entry hero edge = true)
    (t : Transition) (first : step board (entry.at hero) edge.direction = some t) :
    base (entry.at hero) + Int.ofNat (entry.score hero) ≤
      Int.ofNat t.pushCost + base t.state + Int.ofNat (rawBonus table key (normalizer.normalize t.state)) := by
  have parts := Bool.and_eq_true_iff.mp checked
  have actual : step board (entry.at hero) edge.direction = edge.expected := of_decide_eq_true parts.1
  have expected : edge.expected = some t := actual.symm.trans first
  rw [expected] at parts
  cases pushed : t.pushed with
  | true =>
    have finite : pushCheck base normalize key evaluate entry hero t edge.witness = true := by
      simpa only [pushed, ↓reduceIte] using parts.2
    have result := pushCheck_sound base normalize key evaluate entry hero t edge.witness finite
    simpa only [evaluateEq, ← normalizerEq] using result
  | false =>
    have scores : entry.score hero ≤ entry.score t.state.player :=
      of_decide_eq_true (by simpa only [pushed, Bool.false_eq_true, ↓reduceIte] using parts.2)
    have bound := valid (entry.at hero) edge.direction t first
    have same : t.state = entry.at t.state.player := by
      rcases step_cases_full board (entry.at hero) edge.direction t first with walk | push
      · rcases walk with ⟨_, _, _, _, _, shape⟩; subst t; rfl
      · rcases push with ⟨_, _, _, _, _, _, shape⟩; cases t; simp_all
    rw [same, honest]
    rw [same] at bound
    simp only [Int.ofNat_eq_natCast] at bound ⊢
    omega

theorem rowCheck_sound (board : Board) (base : State → Int)
    (normalizer : Normalizer board) (normalize : State → State)
    (table : Table) (key : State → Nat) (evaluate : State → Nat → Nat)
    (entry : Entry) (row : HeroRow)
    (valid : StepBound board base)
    (normalizerEq : ∀ s, normalizer.normalize s = normalize s)
    (evaluateEq : ∀ s, evaluate s (key s) = rawBonus table key s)
    (honest : ∀ p, rawBonus table key (normalizer.normalize (entry.at p)) = entry.score p)
    (checked : rowCheck board base normalize key evaluate entry row = true)
    (direction : Dir) (t : Transition) (first : step board (entry.at row.hero) direction = some t) :
    base (entry.at row.hero) + Int.ofNat (entry.score row.hero) ≤
      Int.ofNat t.pushCost + base t.state + Int.ofNat (rawBonus table key (normalizer.normalize t.state)) := by
  have parts := Bool.and_eq_true_iff.mp checked
  have dmember : direction ∈ allDirs := by cases direction <;> simp [allDirs, cardinalDirs]
  have selected := List.all_eq_true.mp parts.1 direction dmember
  rcases List.any_eq_true.mp selected with ⟨edge, member, same⟩
  have equal : edge.direction = direction := of_decide_eq_true same
  have checkedEdge := List.all_eq_true.mp parts.2 edge member
  apply edgeCheck_sound board base normalizer normalize table key evaluate entry row.hero edge
    valid normalizerEq evaluateEq honest checkedEdge t
  simpa only [equal] using first

theorem check_sound (board : Board) (base : State → Int)
    (normalizer : Normalizer board) (normalize : State → State)
    (table : Table) (key : State → Nat) (evaluate : State → Nat → Nat)
    (entry : Entry) (heroes : List Cell) (rows : List HeroRow)
    (valid : StepBound board base)
    (normalizerEq : ∀ s, normalizer.normalize s = normalize s)
    (evaluateEq : ∀ s, evaluate s (key s) = rawBonus table key s)
    (honest : ∀ p, rawBonus table key (normalizer.normalize (entry.at p)) = entry.score p)
    (limit : ∀ hero, 0 < entry.score hero → hero ∈ heroes)
    (checked : check board base normalize key evaluate entry heroes rows = true) :
    RowBound board base normalizer table key entry := by
  intro hero positive direction t first
  have parts := Bool.and_eq_true_iff.mp checked
  have covered := List.all_eq_true.mp parts.1 hero (limit hero positive)
  rcases Bool.or_eq_true_iff.mp covered with zero | selected
  · have impossible : entry.score hero = 0 := of_decide_eq_true zero; omega
  · rcases List.any_eq_true.mp selected with ⟨row, member, same⟩
    have equal : row.hero = hero := of_decide_eq_true same
    have checkedRow := List.all_eq_true.mp parts.2 row member
    simpa only [equal] using rowCheck_sound board base normalizer normalize table key evaluate entry row
      valid normalizerEq evaluateEq honest checkedRow direction t (by simpa only [equal] using first)

end NetHack.Sokoban.FiniteMatrix
