import Owner1007.GateTokens32
import Owner1007.GroupParity32

namespace Owner1007.GateSurvival32
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.GhostProjection Owner1007.TokenAccounting
open Owner1007.Heavy32 Owner1007.GateTokens32 Owner1007.EnergyFrame32

theorem fixed86_preserves113 {state final : State} {dirs : List Dir} {pushes moves : Nat}
    {outcomes : List Outcome}
    (logged : Logged soko3_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state past pastMoves)
    (occupied : 86 ∈ state.boulders) (fixed : ownPushes [86] outcomes = 0)
    (cell : Cell) (location : cell = 113 ∨ cell = 112)
    (zero : ownSlack p [cell] outcomes = 0) :
    endGroup [cell] outcomes ≠ [] := by
  induction logged generalizing history past pastMoves cell with
  | nil current => simp [endGroup]
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
    have first86 : ownPush [86] outcome = 0 := by simp only [ownPushes] at fixed; omega
    have update86 := ownPush_zero_update [86] outcome first86
    have rest86 : ownPushes [86] outcomes = 0 := by
      simp only [ownPushes, first86, update86, Nat.zero_add] at fixed
      exact fixed
    have subset86 : [86] ⊆ state.boulders := by
      intro c member
      have eq : c = 86 := by simpa using member
      subst c
      exact occupied
    have after86 := GhostSubset.update_subset state t outcome effect [86] (by simp) subset86
    rw [update86] at after86
    have occupiedNext : 86 ∈ t.state.boulders := after86 (by simp)
    have firstNN := projected_slack_nonnegative p [cell] outcome
      (logged_step_slack_nonnegative Generated.soko3_2_potential_valid head effect)
    have restNN := tail.ownSlack_nonnegative Generated.soko3_2_potential_valid (update [cell] outcome)
    have firstZero : slack p (projectedOutcome [cell] outcome) = 0 := by
      change 0 ≤ ownSlack p (update [cell] outcome) outcomes at restNN
      simp only [ownSlack] at zero
      omega
    have restZero : ownSlack p (update [cell] outcome) outcomes = 0 := by
      change 0 ≤ ownSlack p (update [cell] outcome) outcomes at restNN
      simp only [ownSlack] at zero
      omega
    cases outcome with
    | walk target =>
      simpa only [endGroup, update] using
        ih nextReached occupiedNext rest86 cell location restZero
    | push source result =>
      by_cases own : source = cell
      · subst source
        have actualZero : slack p (.push cell result) = 0 := by
          simpa [projectedOutcome] using firstZero
        rcases location with rfl | rfl
        · obtain ⟨resultEq, _, _⟩ := zero_head113 reached head effect actualZero
          subst result
          have nextZero : ownSlack p [112] outcomes = 0 := by
            simpa [update, move, post] using restZero
          have survives := ih nextReached occupiedNext rest86 112 (Or.inr rfl) nextZero
          simpa [endGroup, update, move, post] using survives
        · obtain ⟨_, heroEq, _⟩ := zero_head112 reached head effect actualZero
          have clear := step_player_clear _ _ _ _ head
          exact False.elim (clear.2.2.1 (heroEq ▸ occupied))
      · have absent : source ∉ [cell] := by simp [own]
        have same : update [cell] (.push source result) = [cell] := by
          simp only [update, move, if_neg absent]
        have survives := ih nextReached occupiedNext rest86 cell location (by simpa only [same] using restZero)
        simpa only [endGroup, same] using survives

theorem B_member_energy_zero {dirs final pushes moves outcomes}
    (logged : Logged soko3_2.board soko3_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (small : pushes ≤ 140) (cell : Cell) (member : cell ∈ B) :
    energy potential32 [cell] outcomes = 0 := by
  have tight := tight_budget logged completed small
  have freeB : energy potential32 B outcomes = 0 := by
    unfold energy
    rw [tight.2.2.1, tight.2.2.2.2]
    rfl
  have bound := logged.member_energy_le Generated.soko3_2_potential_valid
    (by decide +kernel) B (by decide +kernel) (by decide +kernel) cell member
  change energy potential32 [cell] outcomes ≤ energy potential32 B outcomes at bound
  rw [freeB] at bound
  have nonnegative := logged.energy_nonnegative Generated.soko3_2_potential_valid [cell]
  change 0 ≤ energy potential32 [cell] outcomes at nonnegative
  omega

theorem token113_consumed {dirs final pushes moves outcomes}
    (logged : Logged soko3_2.board soko3_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (small : pushes ≤ 140) :
    endGroup [113] outcomes = [] := by
  apply Classical.byContradiction
  intro survives
  have free := B_member_energy_zero logged completed small 113 (by decide +kernel)
  have price := survivor_energy potential32 113 outcomes survives
  have debt : -potential32.boulder 113 = 0 := by decide +kernel
  have noPush : ownPushes [113] outcomes = 0 := by
    rw [free, debt] at price
    simp only [Int.ofNat_eq_natCast, Int.zero_add] at price
    omega
  have no139 := fixed113_blocks139 logged (by decide +kernel) noPush
  have moved := token139_moves logged completed small
  omega

theorem token86_consumed {dirs final pushes moves outcomes}
    (logged : Logged soko3_2.board soko3_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (small : pushes ≤ 140) :
    endGroup [86] outcomes = [] := by
  apply Classical.byContradiction
  intro survives
  have free := B_member_energy_zero logged completed small 86 (by decide +kernel)
  have price := survivor_energy potential32 86 outcomes survives
  have debt : -potential32.boulder 86 = 0 := by decide +kernel
  have noPush : ownPushes [86] outcomes = 0 := by
    rw [free, debt] at price
    simp only [Int.ofNat_eq_natCast, Int.zero_add] at price
    omega
  have gone113 := token113_consumed logged completed small
  have free113 := B_member_energy_zero logged completed small 113 (by decide +kernel)
  have zero113 : ownSlack p [113] outcomes = 0 := by
    simpa only [energy, gone113, debtOf, weightSum, Int.add_zero] using free113
  have present := fixed86_preserves113 logged (Trace.nil _) (by decide +kernel) noPush 113 (Or.inl rfl) zero113
  exact present gone113

theorem B_tokens_consumed {dirs final pushes moves outcomes}
    (logged : Logged soko3_2.board soko3_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (small : pushes ≤ 140) :
    ∀ cell ∈ B, endGroup [cell] outcomes = [] := by
  intro cell member
  by_cases is86 : cell = 86
  · subst cell
    exact token86_consumed logged completed small
  by_cases is113 : cell = 113
  · subst cell
    exact token113_consumed logged completed small
  have positive : 0 < -potential32.boulder cell := by
    have finite : ∀ c ∈ B, c ≠ 86 → c ≠ 113 → 0 < -potential32.boulder c := by decide +kernel
    exact finite cell member is86 is113
  apply Classical.byContradiction
  intro survives
  have free := B_member_energy_zero logged completed small cell member
  have price := survivor_energy potential32 cell outcomes survives
  rw [free] at price
  have nonnegative : 0 ≤ Int.ofNat (ownPushes [cell] outcomes) := by simp only [Int.ofNat_eq_natCast]; omega
  omega

#print axioms token113_consumed
#print axioms token86_consumed
#print axioms B_tokens_consumed
end Owner1007.GateSurvival32
