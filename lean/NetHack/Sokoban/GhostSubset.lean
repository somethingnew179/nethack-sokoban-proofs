/- Distinct persistent subsets can be transported together. One group may
subsequently forget entries by a proved sublist; forgotten entries do not
become members of the other group. No search restriction is assumed. -/
import NetHack.Sokoban.GhostPartition
namespace NetHack.Sokoban.GhostSubset
open HazardPattern GhostPartition

theorem erase_subset {small large : List Cell} (subset : small ⊆ large)
    (unique : small.Nodup) (source : Cell) : small.erase source ⊆ large.erase source := by
  intro c member
  have different : c ≠ source := by
    intro same; subst c; exact List.Nodup.not_mem_erase unique member
  exact (List.mem_erase_of_ne different).mpr (subset (List.mem_of_mem_erase member))

theorem update_subset (state : State) (t : Transition) (outcome : Outcome)
    (effect : Matches state t outcome) (group : List Cell) (unique : group.Nodup)
    (subset : group ⊆ state.boulders) : update group outcome ⊆ t.state.boulders := by
  cases outcome with
  | walk target => rw [effect]; exact subset
  | push source result =>
    have erased := erase_subset subset unique source
    by_cases owner : source ∈ group
    · cases result with
      | stay landing =>
        rw [effect.2]
        simp only [update,move,if_pos owner,post]
        exact List.cons_subset_cons _ erased
      | fill hole =>
        rw [effect.2.2]
        simpa only [update,move,if_pos owner,post] using erased
    · have retained : group ⊆ state.boulders.erase source := by
        intro c member
        have different : c ≠ source := by intro same; subst c; exact owner member
        exact (List.mem_erase_of_ne different).mpr (subset member)
      cases result with
      | stay landing =>
        rw [effect.2]
        simp only [update,move,if_neg owner]
        exact fun _ h => List.mem_cons_of_mem _ (retained h)
      | fill hole =>
        rw [effect.2.2]
        simpa only [update,move,if_neg owner] using retained

theorem update_unique (state : State) (t : Transition) (outcome : Outcome)
    (effect : Matches state t outcome) (nextUnique : t.state.boulders.Nodup)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders) :
    (update group outcome).Nodup := by
  cases outcome with
  | walk _ => exact unique
  | push source result =>
    by_cases owner : source ∈ group
    · have erased := erase_subset subset unique source
      cases result with
      | stay landing =>
        rw [effect.2] at nextUnique
        change (landing :: state.boulders.erase source).Nodup at nextUnique
        have fresh := (List.nodup_cons.mp nextUnique).1
        simp only [update,move,if_pos owner,post]
        exact List.nodup_cons.mpr ⟨fun h => fresh (erased h),unique.erase source⟩
      | fill _ => simpa only [update,move,if_pos owner,post] using unique.erase source
    · simp only [update,move,if_neg owner]
      exact unique

theorem pair_update_perm (first second : List Cell) (unique : (first ++ second).Nodup)
    (outcome : Outcome) :
    (update first outcome ++ update second outcome).Perm (update (first ++ second) outcome) := by
  cases outcome with
  | walk _ => exact .refl _
  | push source result =>
    by_cases owner : source ∈ first ++ second
    · have flat := move_flatten [first,second] source result (by simpa using unique) (by simpa using owner)
      simpa only [List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
        update,move,if_pos owner] using flat
    · have one : source ∉ first := fun h => owner (List.mem_append_left _ h)
      have two : source ∉ second := fun h => owner (List.mem_append_right _ h)
      simp only [update,move,if_neg owner,if_neg one,if_neg two]
      exact .refl _

theorem pair_transport (state : State) (t : Transition) (outcome : Outcome)
    (effect : Matches state t outcome) (nextUnique : t.state.boulders.Nodup)
    (first second after : List Cell) (unique : (first ++ second).Nodup)
    (subset : first ++ second ⊆ state.boulders)
    (forgotten : after.Sublist (update first outcome)) :
    (after ++ update second outcome).Nodup ∧ after ++ update second outcome ⊆ t.state.boulders := by
  have canonicalUnique := update_unique state t outcome effect nextUnique (first++second) unique subset
  have canonicalSubset := update_subset state t outcome effect (first++second) unique subset
  have perm := pair_update_perm first second unique outcome
  have splitUnique := perm.nodup_iff.mpr canonicalUnique
  have reduced := forgotten.append (List.Sublist.refl (update second outcome))
  refine ⟨List.Nodup.sublist reduced splitUnique,?_⟩
  intro c member
  exact canonicalSubset (perm.mem_iff.mp (reduced.subset member))

end NetHack.Sokoban.GhostSubset
