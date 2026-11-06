/- Finite residuals of any potential valid on a proved preserved invariant.
The invariant is discharged at the original initial state; no extra premise
is put on the user's original completing Trace. -/
import NetHack.Sokoban.FiniteResidual
namespace NetHack.Sokoban.FiniteResidualGuarded
open LowerBounds StatePermutation FiniteResidual
set_option linter.unusedSimpArgs false

theorem step_bound (base : State → Int) (invariant : State → Prop)
    (normalizer : Normalizer board) (table : Table) (key : State → Nat)
    (valid : ∀ s d t, invariant s → step board s d = some t →
      base s ≤ Int.ofNat t.pushCost + base t.state)
    (respects : ∀ a b, Equivalent a b → base a = base b)
    (rows : All (RowBound board base normalizer table key) table)
    (s : State) (d : Dir) (t : Transition) (invariantState : invariant s)
    (checked : step board s d = some t) :
    corrected base normalizer table key s ≤ Int.ofNat t.pushCost + corrected base normalizer table key t.state := by
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
      have bound := valid s d t invariantState checked
      simp only [corrected, bonus, if_pos good, zero, Int.ofNat_eq_natCast, Int.ofNat_zero, Int.add_zero]
      change base s ≤ Int.ofNat t.pushCost + (base t.state + bonus normalizer table key t.state)
      omega
  · have bound := valid s d t invariantState checked
    simp only [corrected, bonus, if_neg good, Int.add_zero]
    change base s ≤ Int.ofNat t.pushCost + (base t.state + bonus normalizer table key t.state)
    omega

theorem trace_bound (base : State → Int) (invariant : State → Prop)
    (normalizer : Normalizer board) (table : Table) (key : State → Nat)
    (valid : ∀ s d t, invariant s → step board s d = some t →
      base s ≤ Int.ofNat t.pushCost + base t.state)
    (preserved : ∀ s d t, invariant s → step board s d = some t → invariant t.state)
    (respects : ∀ a b, Equivalent a b → base a = base b)
    (rows : All (RowBound board base normalizer table key) table)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) (initialGood : invariant initial) :
    corrected base normalizer table key initial ≤
      Int.ofNat pushes + corrected base normalizer table key final := by
  induction trace with
  | nil => simp
  | cons head tail ih =>
    have first := step_bound base invariant normalizer table key valid respects rows _ _ _ initialGood head
    have rest := ih (preserved _ _ _ initialGood head)
    simp only [Int.ofNat_eq_natCast,Int.natCast_add] at first rest ⊢
    omega

theorem pushes_lower_bound (base : State → Int) (invariant : State → Prop)
    (normalizer : Normalizer board) (table : Table) (key : State → Nat)
    (valid : ∀ s d t, invariant s → step board s d = some t →
      base s ≤ Int.ofNat t.pushCost + base t.state)
    (preserved : ∀ s d t, invariant s → step board s d = some t → invariant t.state)
    (respects : ∀ a b, Equivalent a b → base a = base b)
    (goalBound : ∀ s, Goal s → base s ≤ 0)
    (rows : All (RowBound board base normalizer table key) table)
    (goalFree : All (fun entry => entry.holes ≠ []) table)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (initialGood : invariant initial) (cost : Nat)
    (initialValue : corrected base normalizer table key initial = Int.ofNat cost)
    (trace : Trace board initial directions final pushes moves) (completed : Goal final) : cost ≤ pushes := by
  have total := trace_bound base invariant normalizer table key valid preserved respects rows trace initialGood
  have terminal := FiniteResidual.goalBound base normalizer table key goalBound goalFree final completed
  rw [initialValue] at total
  simp only [Int.ofNat_eq_natCast] at total
  omega
end NetHack.Sokoban.FiniteResidualGuarded
