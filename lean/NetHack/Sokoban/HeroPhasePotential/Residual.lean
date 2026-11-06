/- Guarded finite residuals for the unchanged Model. Positive literal rows
cover actual Model.step, all directions and hero cells. Global validity is
required only on the original proved HazardPhases.Good invariant; no search
quotient is assumed. -/
import NetHack.Sokoban.HeroPhasePotential.Core
import NetHack.Sokoban.FiniteResidual
namespace NetHack.Sokoban.HeroPhasePotential.Residual
open LowerBounds StatePermutation FiniteResidual
set_option linter.unusedSimpArgs false

theorem value_respects {board original phases} (cert : Certificate board original phases)
    (a b : State) (related : Equivalent a b) : value cert a = value cert b := by
  have phase : HazardPhaseCountedCorrection.phaseOf original a =
      HazardPhaseCountedCorrection.phaseOf original b := by
    simp only [HazardPhaseCountedCorrection.phaseOf, related.holes.length_eq]
  simp only [value, valueAt, phase, related.player,
    weightSum_permutation _ related.boulders, weightSum_permutation _ related.holes]

theorem step_bound {board original phases} (cert : Certificate board original phases)
    (normalizer : Normalizer board) (table : Table) (key : State → Nat)
    (rows : All (RowBound board (value cert) normalizer table key) table)
    (s : State) (d : Dir) (t : Transition)
    (phaseGood : HazardPhases.Good phases s) (checked : step board s d = some t) :
    corrected (value cert) normalizer table key s ≤
      Int.ofNat t.pushCost + corrected (value cert) normalizer table key t.state := by
  let base := value cert
  have respects := value_respects cert
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
      have bound := HeroPhasePotential.step_bound cert s d t phaseGood checked
      change base s ≤ Int.ofNat t.pushCost + base t.state at bound
      simp only [corrected, bonus, if_pos good, zero, Int.ofNat_eq_natCast, Int.ofNat_zero, Int.add_zero]
      change base s ≤ Int.ofNat t.pushCost + (base t.state + bonus normalizer table key t.state)
      omega
  · have bound := HeroPhasePotential.step_bound cert s d t phaseGood checked
    change base s ≤ Int.ofNat t.pushCost + base t.state at bound
    simp only [corrected, bonus, if_neg good, Int.add_zero]
    change base s ≤ Int.ofNat t.pushCost + (base t.state + bonus normalizer table key t.state)
    omega


theorem trace_bound {board original phases} (cert : Certificate board original phases)
    (normalizer : Normalizer board) (table : Table) (key : State → Nat)
    (rows : All (RowBound board (value cert) normalizer table key) table)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves)
    (initialGood : HazardPhases.Good phases initial) :
    corrected (value cert) normalizer table key initial ≤
      Int.ofNat pushes + corrected (value cert) normalizer table key final := by
  induction trace with
  | nil => simp
  | cons head tail ih =>
    have first := step_bound cert normalizer table key rows _ _ _ initialGood head
    have rest := ih (HazardPhases.step_good phases _ _ _ initialGood head)
    simp only [Int.ofNat_eq_natCast, Int.natCast_add] at first rest ⊢
    omega

theorem pushes_lower_bound {board original phases} (cert : Certificate board original phases)
    (normalizer : Normalizer board) (table : Table) (key : State → Nat)
    (rows : All (RowBound board (value cert) normalizer table key) table)
    (goalFree : All (fun entry => entry.holes ≠ []) table)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (initialGood : HazardPhases.Good phases initial) (cost : Nat)
    (initialValue : corrected (value cert) normalizer table key initial = Int.ofNat cost)
    (trace : Trace board initial directions final pushes moves) (completed : Goal final) :
    cost ≤ pushes := by
  have total := trace_bound cert normalizer table key rows trace initialGood
  have terminal := FiniteResidual.goalBound (value cert) normalizer table key
    (fun s done => HeroPhasePotential.goal_bound cert s done) goalFree final completed
  rw [initialValue] at total
  simp only [Int.ofNat_eq_natCast] at total
  omega
end NetHack.Sokoban.HeroPhasePotential.Residual
