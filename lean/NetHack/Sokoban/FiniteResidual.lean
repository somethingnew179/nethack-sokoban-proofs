/- Finite corrections of a previously proved universal potential. Every
positive row must cover ALL actual Model actions at every selected hero cell.
Search order, region compression, matching and external pruning are absent
from this theorem. Finite row obligations remain to be proved for each table. -/
import NetHack.Sokoban.StatePermutation

set_option linter.unusedSimpArgs false
namespace NetHack.Sokoban.FiniteResidual
open LowerBounds StatePermutation

structure Entry where
  boulders : List Cell
  holes : List Cell
  score : Cell → Nat

def Entry.at (e : Entry) (hero : Cell) : State := ⟨hero, e.boulders, e.holes⟩

inductive Table where
  | empty
  | node (key : Nat) (entry : Entry) (left right : Table)

def lookup : Table → Nat → Option Entry
  | .empty, _ => none
  | .node k e left right, q =>
    if q = k then some e else if q < k then lookup left q else lookup right q

def All (property : Entry → Prop) : Table → Prop
  | .empty => True
  | .node _ e left right => property e ∧ All property left ∧ All property right

theorem lookup_all (property : Entry → Prop) (table : Table)
    (all : All property table) (key : Nat) (entry : Entry)
    (found : lookup table key = some entry) : property entry := by
  induction table with
  | empty => simp [lookup] at found
  | node k e left right il ir =>
    simp only [lookup] at found
    split at found
    · cases found; exact all.1
    · split at found
      · exact il all.2.1 found
      · exact ir all.2.2 found

/-- A wrong key, malformed tree or collision cannot invent a match: both
canonical occupancy lists must also agree exactly with the selected entry. -/
def rawBonus (table : Table) (key : State → Nat) (state : State) : Nat :=
  match lookup table (key state) with
  | none => 0
  | some entry =>
    if state.boulders = entry.boulders ∧ state.holes = entry.holes then
      entry.score state.player else 0

theorem positive_row (property : Entry → Prop) (table : Table) (key : State → Nat)
    (all : All property table) (s : State) (positive : 0 < rawBonus table key s) :
    ∃ e, property e ∧ s = e.at s.player ∧ rawBonus table key s = e.score s.player := by
  unfold rawBonus at positive ⊢
  cases found : lookup table (key s) with
  | none => simp [found] at positive
  | some e =>
    simp only [found] at positive ⊢
    split at positive
    next matchLists =>
      refine ⟨e, lookup_all property table all _ e found, ?_, if_pos matchLists⟩
      cases s
      simp_all [Entry.at]
    next => simp_all

structure Normalizer (board : Board) where
  good : State → Prop
  decidableGood : ∀ s, Decidable (good s)
  normalize : State → State
  equivalent : ∀ s, good s → Equivalent s (normalize s)
  respects : ∀ a b, Equivalent a b → normalize a = normalize b
  preserved : ∀ s d t, good s → step board s d = some t → good t.state

attribute [instance] Normalizer.decidableGood

def bonus (normalizer : Normalizer board) (table : Table) (key : State → Nat)
    (s : State) : Int :=
  if normalizer.good s then Int.ofNat (rawBonus table key (normalizer.normalize s)) else 0

def corrected (base : State → Int) (normalizer : Normalizer board)
    (table : Table) (key : State → Nat) (s : State) : Int :=
  base s + bonus normalizer table key s

def RowBound (board : Board) (base : State → Int) (normalizer : Normalizer board)
    (table : Table) (key : State → Nat) (e : Entry) : Prop :=
  ∀ hero, 0 < e.score hero → ∀ direction t,
    step board (e.at hero) direction = some t →
    base (e.at hero) + Int.ofNat (e.score hero) ≤
      Int.ofNat t.pushCost + base t.state + Int.ofNat (rawBonus table key (normalizer.normalize t.state))

def rowCheck (board : Board) (base : State → Int) (normalizer : Normalizer board)
    (table : Table) (key : State → Nat) (heroes : List Cell) (e : Entry) : Bool :=
  heroes.all fun hero =>
    if e.score hero = 0 then true else
      allDirs.all fun direction =>
        match step board (e.at hero) direction with
        | none => true
        | some t => decide (base (e.at hero) + Int.ofNat (e.score hero) ≤
            Int.ofNat t.pushCost + base t.state + Int.ofNat (rawBonus table key (normalizer.normalize t.state)))

theorem rowCheck_sound (board : Board) (base : State → Int) (normalizer : Normalizer board)
    (table : Table) (key : State → Nat) (heroes : List Cell) (e : Entry)
    (coverage : ∀ hero, 0 < e.score hero → hero ∈ heroes)
    (checked : rowCheck board base normalizer table key heroes e = true) :
    RowBound board base normalizer table key e := by
  intro hero positive direction t first
  have numeric := List.all_eq_true.mp checked hero (coverage hero positive)
  simp only [show ¬ e.score hero = 0 by omega, ↓reduceIte] at numeric
  have member : direction ∈ allDirs := by cases direction <;> simp [allDirs, cardinalDirs]
  have actual := List.all_eq_true.mp numeric direction member
  rw [first] at actual
  exact of_decide_eq_true actual

/-- The executable evaluator may be replaced by a separately proved equal
function. This avoids repeatedly reducing a large tree as a data argument;
the equality premise is universal, not a native evaluation assumption. -/
def rowCheckUsing (board : Board) (base : State → Int) (evaluate : State → Nat)
    (heroes : List Cell) (e : Entry) : Bool :=
  heroes.all fun hero =>
    if e.score hero = 0 then true else allDirs.all fun direction =>
      match step board (e.at hero) direction with
      | none => true
      | some t => decide (base (e.at hero) + Int.ofNat (e.score hero) ≤
          Int.ofNat t.pushCost + base t.state + Int.ofNat (evaluate t.state))

theorem rowCheckUsing_sound (board : Board) (base : State → Int) (normalizer : Normalizer board)
    (table : Table) (key : State → Nat) (evaluate : State → Nat) (heroes : List Cell) (e : Entry)
    (coverage : ∀ hero, 0 < e.score hero → hero ∈ heroes)
    (agrees : ∀ s, evaluate s = rawBonus table key (normalizer.normalize s))
    (checked : rowCheckUsing board base evaluate heroes e = true) :
    RowBound board base normalizer table key e := by
  apply rowCheck_sound board base normalizer table key heroes e coverage
  simpa only [rowCheckUsing, rowCheck, agrees] using checked

def checkAll (check : Entry → Bool) : Table → Bool
  | .empty => true
  | .node _ e left right => check e && checkAll check left && checkAll check right

theorem checkAll_sound (property : Entry → Prop) (check : Entry → Bool)
    (sound : ∀ e, check e = true → property e) (table : Table)
    (checked : checkAll check table = true) : All property table := by
  induction table with
  | empty => trivial
  | node k e left right il ir =>
    have parts := Bool.and_eq_true_iff.mp checked
    have first := Bool.and_eq_true_iff.mp parts.1
    exact ⟨sound e first.1, il first.2, ir parts.2⟩

def finiteScore (area ones twos hero : Nat) : Nat :=
  if hero < area then if twos.testBit hero then 2 else if ones.testBit hero then 1 else 0 else 0

theorem finiteScore_coverage (area ones twos hero : Nat) (positive : 0 < finiteScore area ones twos hero) :
    hero ∈ List.range area := by
  apply List.mem_range.mpr
  by_cases bound : hero < area
  · exact bound
  · simp [finiteScore, bound] at positive

def fastRowCheck (board : Board) (base : State → Int) (normalizer : Normalizer board)
    (table : Table) (key : State → Nat) (heroes : List Cell) (e : Entry) : Bool :=
  heroes.all fun hero =>
    if e.score hero = 0 then true else
      allDirs.all fun direction =>
        match step board (e.at hero) direction with
        | none => true
        | some t => if t.pushed then
            decide (base (e.at hero) + Int.ofNat (e.score hero) ≤
              Int.ofNat t.pushCost + base t.state + Int.ofNat (rawBonus table key (normalizer.normalize t.state)))
          else decide (e.score hero ≤ e.score t.state.player)

theorem honest_of_found (normalizer : Normalizer board) (table : Table) (key : State → Nat) (e : Entry)
    (canonical : ∀ hero, normalizer.normalize (e.at hero) = e.at hero)
    (ignoresHero : ∀ hero, key (e.at hero) = key (e.at 0))
    (found : lookup table (key (e.at 0)) = some e) :
    ∀ hero, rawBonus table key (normalizer.normalize (e.at hero)) = e.score hero := by
  intro hero
  rw [canonical hero]
  unfold rawBonus
  rw [ignoresHero hero, found]
  simp [Entry.at]

theorem fastRowCheck_sound (board : Board) (base : State → Int) (normalizer : Normalizer board)
    (table : Table) (key : State → Nat) (heroes : List Cell) (e : Entry)
    (valid : StepBound board base)
    (coverage : ∀ hero, 0 < e.score hero → hero ∈ heroes)
    (honest : ∀ hero, rawBonus table key (normalizer.normalize (e.at hero)) = e.score hero)
    (checked : fastRowCheck board base normalizer table key heroes e = true) :
    RowBound board base normalizer table key e := by
  intro hero positive direction t first
  have numeric := List.all_eq_true.mp checked hero (coverage hero positive)
  simp only [show ¬ e.score hero = 0 by omega, ↓reduceIte] at numeric
  have member : direction ∈ allDirs := by cases direction <;> simp [allDirs, cardinalDirs]
  have actual := List.all_eq_true.mp numeric direction member
  rw [first] at actual
  cases pushed : t.pushed with
  | true =>
    simp only [pushed, ↓reduceIte] at actual
    exact of_decide_eq_true actual
  | false =>
    have scores : e.score hero ≤ e.score t.state.player := by
      exact of_decide_eq_true (by simpa only [pushed, Bool.false_eq_true, ↓reduceIte] using actual)
    have bound := valid (e.at hero) direction t first
    have same : t.state = e.at t.state.player := by
      rcases step_cases_full board (e.at hero) direction t first with walk | push
      · rcases walk with ⟨target, _, _, _, _, shape⟩
        subst t
        rfl
      · rcases push with ⟨_, _, _, _, _, _, shape⟩
        cases t
        simp_all
    rw [same, honest]
    rw [same] at bound
    simp only [Int.ofNat_eq_natCast] at bound ⊢
    omega

def fastRowCheckUsing (board : Board) (base : State → Int) (evaluate : State → Nat)
    (heroes : List Cell) (e : Entry) : Bool :=
  heroes.all fun hero =>
    if e.score hero = 0 then true else allDirs.all fun direction =>
      match step board (e.at hero) direction with
      | none => true
      | some t => if t.pushed then
          decide (base (e.at hero) + Int.ofNat (e.score hero) ≤
            Int.ofNat t.pushCost + base t.state + Int.ofNat (evaluate t.state))
        else decide (e.score hero ≤ e.score t.state.player)

theorem fastRowCheckUsing_sound (board : Board) (base : State → Int) (normalizer : Normalizer board)
    (table : Table) (key : State → Nat) (evaluate : State → Nat) (heroes : List Cell) (e : Entry)
    (valid : StepBound board base)
    (coverage : ∀ hero, 0 < e.score hero → hero ∈ heroes)
    (agrees : ∀ s, evaluate s = rawBonus table key (normalizer.normalize s))
    (honest : ∀ hero, rawBonus table key (normalizer.normalize (e.at hero)) = e.score hero)
    (checked : fastRowCheckUsing board base evaluate heroes e = true) :
    RowBound board base normalizer table key e := by
  apply fastRowCheck_sound board base normalizer table key heroes e valid coverage honest
  simpa only [fastRowCheckUsing, fastRowCheck, agrees] using checked

theorem stepBound (base : State → Int) (normalizer : Normalizer board)
    (table : Table) (key : State → Nat)
    (valid : StepBound board base)
    (respects : ∀ a b, Equivalent a b → base a = base b)
    (rows : All (RowBound board base normalizer table key) table) :
    StepBound board (corrected base normalizer table key) := by
  intro s d t checked
  have positiveNext : 0 ≤ bonus normalizer table key t.state := by
    unfold bonus
    split <;> (try simp only [Int.ofNat_eq_natCast]) <;> omega
  by_cases good : normalizer.good s
  · have goodNext := normalizer.preserved s d t good checked
    by_cases positive : 0 < rawBonus table key (normalizer.normalize s)
    · rcases positive_row _ table key rows _ positive with ⟨entry, row, same, score⟩
      have equivalent := normalizer.equivalent s good
      have normalizedHero : (normalizer.normalize s).player = s.player := equivalent.player.symm
      have matched : normalizer.normalize s = entry.at s.player := by simpa only [normalizedHero] using same
      have related : Equivalent s (entry.at s.player) := matched ▸ equivalent
      rcases step_transport board related d checked with ⟨other, first, paired⟩
      have scorePositive : 0 < entry.score s.player := by simpa only [score, normalizedHero] using positive
      have finite := row s.player scorePositive d other first
      have baseBefore := respects s (entry.at s.player) related
      have baseAfter := respects t.state other.state paired.state
      have normalizedAfter := normalizer.respects t.state other.state paired.state
      have costs : t.pushCost = other.pushCost := by simp only [Transition.pushCost, paired.pushed]
      simp only [corrected, bonus, if_pos good, if_pos goodNext]
      rw [score, normalizedHero, baseBefore, baseAfter, normalizedAfter, costs]
      omega
    · have zero : rawBonus table key (normalizer.normalize s) = 0 := by omega
      have bound := valid s d t checked
      simp only [corrected, bonus, if_pos good, zero, Int.ofNat_eq_natCast, Int.ofNat_zero, Int.add_zero]
      change base s ≤ Int.ofNat t.pushCost + (base t.state + bonus normalizer table key t.state)
      omega
  · have bound := valid s d t checked
    simp only [corrected, bonus, if_neg good, Int.add_zero]
    change base s ≤ Int.ofNat t.pushCost + (base t.state + bonus normalizer table key t.state)
    omega

theorem goalBound (base : State → Int) (normalizer : Normalizer board)
    (table : Table) (key : State → Nat)
    (valid : ∀ s, Goal s → base s ≤ 0)
    (goalFree : All (fun e => e.holes ≠ []) table) :
    ∀ s, Goal s → corrected base normalizer table key s ≤ 0 := by
  intro s completed
  have bound := valid s completed
  by_cases good : normalizer.good s
  · have done := (goal_permutation (normalizer.equivalent s good)).mp completed
    have zero : rawBonus table key (normalizer.normalize s) = 0 := by
      by_cases nz : rawBonus table key (normalizer.normalize s) = 0
      · exact nz
      apply False.elim
      have positive : 0 < rawBonus table key (normalizer.normalize s) := by omega
      rcases positive_row _ table key goalFree _ positive with ⟨entry, forbidden, same, _⟩
      have holes := congrArg State.holes same
      simp only [Entry.at] at holes
      exact forbidden (holes ▸ done)
    simpa only [corrected, bonus, if_pos good, zero, Int.ofNat_eq_natCast, Int.ofNat_zero, Int.add_zero] using bound
  · simpa only [corrected, bonus, if_neg good, Int.add_zero] using bound

end NetHack.Sokoban.FiniteResidual
