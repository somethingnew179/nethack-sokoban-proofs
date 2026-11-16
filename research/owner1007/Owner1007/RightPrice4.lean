import Owner1007.RightPrice4Matrix
namespace Owner1007.RightPrice4
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Q : List Cell := [141,168,246,271]
theorem lock_unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem terminal_phase : ∀ i, (locks i).length ≤ 2 → credit i = 0 := by decide +kernel

theorem q_energy_two {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) : 2 ≤ energy p Q outcomes := by
  have closed := PricedCorral.closed_of_check _ _ _ _ _ _ matrix
  obtain ⟨j,heroInside,locksInside,price⟩ := owned_trace_price closed lock_unique
    logged (Trace.nil _) Q (by decide +kernel) (by decide +kernel)
    (i:=0) (by decide +kernel) (by decide +kernel)
  have endInside := logged.end_subset (by decide +kernel) Q (by decide +kernel) (by decide +kernel)
  have lockInside : locks j ⊆ final.boulders := fun _ h => endInside.2 (locksInside h)
  have conserved := logged.trace.conservation
  have empty : final.holes = [] := completed
  change 20 + final.holes.length = final.boulders.length + 18 at conserved
  rw [empty] at conserved
  simp only [List.length_nil] at conserved
  have count := List.Nodup.length_le_of_subset (lock_unique j) lockInside
  have terminal := terminal_phase j (by omega)
  have initial : credit (0 : Fin 7) = 2 := rfl
  rw [initial,terminal] at price
  have debt := NonlinearFacts.weightSum_nonnegative (fun c => -p.boulder c)
    (endGroup Q outcomes) (fun c => by have h := Generated.soko1_2_potential_valid.nonpositive c; change p.boulder c ≤ 0 at h; omega)
  change 0 ≤ debtOf p (endGroup Q outcomes) at debt
  unfold energy
  omega

def P : List Cell := [192,193,218]
theorem p_energy_two {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) : 2 ≤ energy p P outcomes := by
  have bound := RightEnergy12.raw_group_energy logged (Trace.nil _) P
    (by decide +kernel) (by decide +kernel) completed
  have bonus : RightEnergy12.cert.bonus soko1_2.initial.player
      (PatternCorrection.project P) = 2 := by decide +kernel
  rw [bonus] at bound
  exact bound

theorem right_energy_four {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) : 4 ≤ energy p RightEnergy12.Right outcomes := by
  have ep := p_energy_two logged completed
  have eq := q_energy_two logged completed
  have split := logged.energy_split (by decide +kernel) p P Q (by decide +kernel) (by decide +kernel)
  have perm : (P ++ Q).Perm RightEnergy12.Right := by decide +kernel
  have same := energy_perm p perm outcomes
  omega

#print axioms q_energy_two
#print axioms right_energy_four
end Owner1007.RightPrice4
