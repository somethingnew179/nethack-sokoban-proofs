import Owner1007.TokenBounds32
import Owner1007.Heavy32

namespace Owner1007.TokenAccounting
open NetHack.Sokoban NetHack.Sokoban.LowerBounds

theorem Logged.energy_even_of_singletons {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (actualUnique : initial.boulders.Nodup) (potential : Potential) (group : List Cell)
    (unique : group.Nodup) (subset : group ⊆ initial.boulders)
    (singletons : ∀ cell ∈ group, energy potential [cell] outcomes % 2 = 0) :
    energy potential group outcomes % 2 = 0 := by
  induction group with
  | nil =>
    simp only [energy, Heavy32.ownSlack_empty, endGroup_empty, debtOf, weightSum, Int.zero_add]
    rfl
  | cons cell rest ih =>
    have splitUnique : ([cell] ++ rest).Nodup := unique
    have splitSubset : [cell] ++ rest ⊆ initial.boulders := subset
    have split := logged.energy_split actualUnique potential [cell] rest splitUnique splitSubset
    have tailUnique := (List.nodup_cons.mp unique).2
    have tailSubset : rest ⊆ initial.boulders := fun c h => subset (List.mem_cons_of_mem _ h)
    have tailEven := ih tailUnique tailSubset (fun c h => singletons c (List.mem_cons_of_mem _ h))
    have headEven := singletons cell (by simp)
    change energy potential (cell :: rest) outcomes =
      energy potential [cell] outcomes + energy potential rest outcomes at split
    rw [split]
    omega

end Owner1007.TokenAccounting

namespace Owner1007.EnergyFrame32
open NetHack.Sokoban NetHack.Sokoban.LowerBounds Owner1007.TokenAccounting

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem heavy_initial_debt : ∀ cell ∈ G, cell ≠ 139 → 7 ≤ -potential32.boulder cell := by
  decide +kernel

theorem g_subset : G ⊆ soko3_2.initial.boulders :=
  fun _ h => initial_partition.mem_iff.mp (List.mem_append_left _ h)

theorem heavy_energy_even {dirs final pushes moves outcomes}
    (logged : Logged soko3_2.board soko3_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (small : pushes ≤ 140) (cell : Cell) (member : cell ∈ G)
    (heavy : cell ≠ 139) :
    endGroup [cell] outcomes = [] ∧ energy potential32 [cell] outcomes % 2 = 0 := by
  have budget := (tight_budget logged completed small).1
  have bound := logged.member_energy_le Generated.soko3_2_potential_valid
    (by decide +kernel) G (List.nodup_append.mp initial_unique).1 g_subset cell member
  change energy potential32 [cell] outcomes ≤ energy potential32 G outcomes at bound
  rw [budget] at bound
  have debt := heavy_initial_debt cell member heavy
  have empty : endGroup [cell] outcomes = [] := by
    by_cases empty : endGroup [cell] outcomes = []
    · exact empty
    · have ledger := survivor_energy potential32 cell outcomes empty
      have nonnegative : 0 ≤ Int.ofNat (ownPushes [cell] outcomes) := by
        simp only [Int.ofNat_eq_natCast]
        omega
      omega
  have same : energy potential32 [cell] outcomes = ownSlack potential32 [cell] outcomes := by
    simp only [energy, empty, debtOf, weightSum, Int.add_zero]
  have cheap : ownSlack Heavy32.p [cell] outcomes < -Heavy32.p.boulder cell := by
    change ownSlack potential32 [cell] outcomes < -potential32.boulder cell
    rw [same] at bound
    omega
  have even := Heavy32.cheap_token_even logged (Trace.nil _) cell cheap
  change ownSlack potential32 [cell] outcomes % 2 = 0 at even
  exact ⟨empty, by rw [same]; exact even⟩

/-- An odd five-unit group budget cannot be paid by the six heavy tokens:
their full consumed trajectories have even slack. Thus139 really moves. -/
theorem token139_moves {dirs final pushes moves outcomes}
    (logged : Logged soko3_2.board soko3_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (small : pushes ≤ 140) : 0 < ownPushes [139] outcomes := by
  by_cases zero : ownPushes [139] outcomes = 0
  · have fixed := no_push_unchanged [139] outcomes zero
    have survives : endGroup [139] outcomes ≠ [] := by rw [fixed]; simp
    have price := survivor_energy potential32 139 outcomes survives
    have debt : -potential32.boulder 139 = 0 := by decide +kernel
    have free : energy potential32 [139] outcomes = 0 := by rw [debt, zero] at price; exact price
    have allEven : ∀ cell ∈ G, energy potential32 [cell] outcomes % 2 = 0 := by
      intro cell member
      by_cases same : cell = 139
      · subst cell
        rw [free]
        rfl
      · exact (heavy_energy_even logged completed small cell member same).2
    have even := logged.energy_even_of_singletons (by decide +kernel) potential32 G
      (List.nodup_append.mp initial_unique).1 g_subset allEven
    have budget := (tight_budget logged completed small).1
    rw [budget] at even
    omega
  · omega

#print axioms heavy_energy_even
#print axioms token139_moves
end Owner1007.EnergyFrame32
