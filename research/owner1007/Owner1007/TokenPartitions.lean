import Owner1007.TokenAccounting

namespace Owner1007.TokenAccounting
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.GhostProjection

def energy (potential : Potential) (group : List Cell) (outcomes : List Outcome) : Int :=
  ownSlack potential group outcomes + debtOf potential (endGroup group outcomes)

theorem debtOf_append (potential : Potential) (first second : List Cell) :
    debtOf potential (first ++ second) = debtOf potential first + debtOf potential second := by
  induction first with
  | nil => simp [debtOf, weightSum]
  | cons c rest ih =>
    change -potential.boulder c + debtOf potential (rest ++ second) =
      (-potential.boulder c + debtOf potential rest) + debtOf potential second
    rw [ih]
    omega

theorem debtOf_perm (potential : Potential) {first second : List Cell} (same : first.Perm second) :
    debtOf potential first = debtOf potential second :=
  StatePermutation.weightSum_permutation _ same

theorem update_perm {first second : List Cell} (same : first.Perm second) (outcome : Outcome) :
    (update first outcome).Perm (update second outcome) := by
  cases outcome with
  | walk _ => exact same
  | push source result =>
    by_cases owner : source ∈ first
    · have other := same.mem_iff.mp owner
      cases result <;> simp only [update, move, if_pos owner, if_pos other, post]
      · exact (same.erase source).cons _
      · exact same.erase source
    · have other : source ∉ second := fun h => owner (same.mem_iff.mpr h)
      simp only [update, move, if_neg owner, if_neg other]
      exact same

theorem projected_perm {first second : List Cell} (same : first.Perm second) (outcome : Outcome) :
    projectedOutcome first outcome = projectedOutcome second outcome := by
  cases outcome with
  | walk _ => rfl
  | push source result => simp only [projectedOutcome, same.mem_iff]

theorem endGroup_perm {first second : List Cell} (same : first.Perm second) (outcomes : List Outcome) :
    (endGroup first outcomes).Perm (endGroup second outcomes) := by
  induction outcomes generalizing first second with
  | nil => exact same
  | cons outcome rest ih => exact ih (update_perm same outcome)

theorem ownSlack_perm (potential : Potential) {first second : List Cell}
    (same : first.Perm second) (outcomes : List Outcome) :
    ownSlack potential first outcomes = ownSlack potential second outcomes := by
  induction outcomes generalizing first second with
  | nil => rfl
  | cons outcome rest ih =>
    simp only [ownSlack, projected_perm same outcome, ih (update_perm same outcome)]

theorem energy_perm (potential : Potential) {first second : List Cell}
    (same : first.Perm second) (outcomes : List Outcome) :
    energy potential first outcomes = energy potential second outcomes := by
  unfold energy
  rw [ownSlack_perm potential same outcomes, debtOf_perm potential (endGroup_perm same outcomes)]

theorem energy_cons (potential : Potential) (group : List Cell) (outcome : Outcome) (rest : List Outcome) :
    energy potential group (outcome :: rest) = slack potential (projectedOutcome group outcome) +
      energy potential (update group outcome) rest := by
  simp only [energy, ownSlack, endGroup]
  omega

theorem split_step_slack (potential : Potential) (first second : List Cell)
    (unique : (first ++ second).Nodup) (outcome : Outcome) :
    slack potential (projectedOutcome (first ++ second) outcome) =
      slack potential (projectedOutcome first outcome) + slack potential (projectedOutcome second outcome) := by
  cases outcome with
  | walk _ => simp [projectedOutcome, slack]
  | push source result =>
    have separate := (List.nodup_append.mp unique).2.2
    by_cases one : source ∈ first
    · have two : source ∉ second := fun h => separate source one source h rfl
      have both : source ∈ first ++ second := List.mem_append_left _ one
      simp only [projectedOutcome, if_pos one, if_neg two, if_pos both, slack, Int.add_zero]
    · by_cases two : source ∈ second
      · have both : source ∈ first ++ second := List.mem_append_right _ two
        simp only [projectedOutcome, if_neg one, if_pos two, if_pos both, slack, Int.zero_add]
      · have both : source ∉ first ++ second := by simpa only [List.mem_append, not_or] using And.intro one two
        simp only [projectedOutcome, if_neg one, if_neg two, if_neg both, slack, Int.zero_add]

/-- Exact partitioning of one scalar slack budget; neither disjoint group may
spend the other's pushes or terminal debt. -/
theorem Logged.energy_split {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (actualUnique : initial.boulders.Nodup) (potential : Potential) (first second : List Cell)
    (unique : (first ++ second).Nodup) (subset : first ++ second ⊆ initial.boulders) :
    energy potential (first ++ second) outcomes = energy potential first outcomes + energy potential second outcomes := by
  induction logged generalizing first second with
  | nil => simpa only [energy, ownSlack, endGroup, Int.zero_add] using debtOf_append potential first second
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
    have bothUnique := GhostSubset.update_unique _ _ _ effect nextActual (first++second) unique subset
    have bothSubset := GhostSubset.update_subset _ _ _ effect (first++second) unique subset
    have pair := GhostSubset.pair_update_perm first second unique outcome
    have nextUnique := pair.nodup_iff.mpr bothUnique
    have nextSubset : update first outcome ++ update second outcome ⊆ t.state.boulders :=
      fun _ h => bothSubset (pair.mem_iff.mp h)
    have restBound := ih nextActual (update first outcome) (update second outcome) nextUnique nextSubset
    have same := energy_perm potential pair outcomes
    have firstBound := split_step_slack potential first second unique outcome
    rw [energy_cons, energy_cons, energy_cons]
    omega

theorem matches_full_update (state : State) (t : Transition) (outcome : Outcome)
    (effect : Matches state t outcome) :
    update state.boulders outcome = t.state.boulders ∧ projectedOutcome state.boulders outcome = outcome := by
  have updated := GhostOracleFacts.matches_update state t outcome effect
  refine ⟨updated.symm, ?_⟩
  cases outcome with
  | walk _ => rfl
  | push source result =>
    have owner : source ∈ state.boulders := by cases result <;> exact effect.1
    simp only [projectedOutcome, if_pos owner]

theorem Logged.all_energy {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes) (potential : Potential) :
    potential.value initial + energy potential initial.boulders outcomes =
      Int.ofNat pushes + weightSum potential.hole final.holes := by
  induction logged with
  | nil =>
    simp only [energy, ownSlack, endGroup, Int.zero_add, Int.ofNat_eq_natCast, Int.natCast_zero]
    rw [debtOf_neg]
    simp only [Potential.value]
    omega
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have exactUpdate := matches_full_update state t outcome effect
    have delta := matches_delta potential state t outcome effect
    rw [energy_cons, exactUpdate.1, exactUpdate.2]
    simp only [Int.ofNat_eq_natCast, Int.natCast_add] at delta ih ⊢
    omega

theorem Logged.energy_nonnegative {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    {potential : Potential} (valid : Valid board potential) (group : List Cell) :
    0 ≤ energy potential group outcomes := by
  have cost := logged.ownSlack_nonnegative valid group
  have debt := NonlinearFacts.weightSum_nonnegative (fun c => -potential.boulder c)
    (endGroup group outcomes) (fun c => by have h := valid.nonpositive c; omega)
  change 0 ≤ debtOf potential (endGroup group outcomes) at debt
  unfold energy
  omega

#print axioms Logged.energy_split
#print axioms Logged.all_energy
end Owner1007.TokenAccounting
