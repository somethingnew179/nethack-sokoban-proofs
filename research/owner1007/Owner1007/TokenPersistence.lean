import Owner1007.TokenPartitions

namespace Owner1007.TokenAccounting
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.GhostProjection

theorem update_mono (small large : List Cell) (unique : small.Nodup)
    (subset : small ⊆ large) (outcome : Outcome) : update small outcome ⊆ update large outcome := by
  cases outcome with
  | walk _ => exact subset
  | push source result =>
    by_cases own : source ∈ small
    · have largeOwn := subset own
      have erased := GhostSubset.erase_subset subset unique source
      cases result <;> simp only [update, move, if_pos own, if_pos largeOwn, post]
      · exact List.cons_subset_cons _ erased
      · exact erased
    · by_cases largeOwn : source ∈ large
      · have kept : small ⊆ large.erase source := by
          intro c member
          have different : c ≠ source := by intro same; exact own (same ▸ member)
          exact (List.mem_erase_of_ne different).mpr (subset member)
        cases result <;> simp only [update, move, if_neg own, if_pos largeOwn, post]
        · exact fun _ h => List.mem_cons_of_mem _ (kept h)
        · exact kept
      · simp only [update, move, if_neg own, if_neg largeOwn]
        exact subset

theorem projected_slack_mono (potential : Potential) (small large : List Cell)
    (subset : small ⊆ large) (outcome : Outcome) (nonnegative : 0 ≤ slack potential outcome) :
    slack potential (projectedOutcome small outcome) ≤ slack potential (projectedOutcome large outcome) := by
  cases outcome with
  | walk _ => exact Int.le_refl _
  | push source result =>
    by_cases own : source ∈ small
    · have largeOwn := subset own
      simp only [projectedOutcome, if_pos own, if_pos largeOwn]
      exact Int.le_refl _
    · by_cases largeOwn : source ∈ large
      · simpa only [projectedOutcome, if_neg own, if_pos largeOwn, slack] using nonnegative
      · simp only [projectedOutcome, if_neg own, if_neg largeOwn]
        exact Int.le_refl _

theorem endGroup_empty (outcomes : List Outcome) : endGroup [] outcomes = [] := by
  induction outcomes with
  | nil => rfl
  | cons outcome rest ih =>
    cases outcome with
    | walk _ => exact ih
    | push source result => simpa only [endGroup, update, move, List.not_mem_nil, if_false] using ih

theorem endGroup_length_le (group : List Cell) (outcomes : List Outcome) :
    (endGroup group outcomes).length ≤ group.length := by
  induction outcomes generalizing group with
  | nil => exact Nat.le_refl _
  | cons outcome rest ih => exact Nat.le_trans (ih _) (update_length group outcome)

theorem ownPush_zero_update (group : List Cell) (outcome : Outcome)
    (zero : ownPush group outcome = 0) : update group outcome = group := by
  cases outcome with
  | walk _ => rfl
  | push source result =>
    have absent : source ∉ group := by
      intro owner
      simp only [ownPush, if_pos owner] at zero
      omega
    simp only [update, move, if_neg absent]

theorem no_push_unchanged (group : List Cell) (outcomes : List Outcome)
    (zero : ownPushes group outcomes = 0) : endGroup group outcomes = group := by
  induction outcomes generalizing group with
  | nil => rfl
  | cons outcome rest ih =>
    have first : ownPush group outcome = 0 := by simp only [ownPushes] at zero; omega
    have same := ownPush_zero_update group outcome first
    simp only [ownPushes, first, Nat.zero_add, same] at zero
    simpa only [endGroup, same] using ih group zero

/-- A singleton that is still present has never received absorption credit.
This closes the gap between the group ledger and persistent-identity counting. -/
theorem survivor_credits_zero (potential : Potential) (group : List Cell)
    (outcomes : List Outcome) (single : group.length ≤ 1)
    (survives : endGroup group outcomes ≠ []) : ownCredits potential group outcomes = 0 := by
  induction outcomes generalizing group with
  | nil => rfl
  | cons outcome rest ih =>
    have nextSingle := Nat.le_trans (update_length group outcome) single
    have nextSurvives : endGroup (update group outcome) rest ≠ [] := survives
    have restZero := ih (update group outcome) nextSingle nextSurvives
    have firstZero : ownCredit potential group outcome = 0 := by
      cases outcome with
      | walk _ => rfl
      | push source result =>
        cases result with
        | stay _ => rfl
        | fill hole =>
          by_cases owner : source ∈ group
          · have erased := List.length_erase_of_mem owner
            have lengthZero : (group.erase source).length = 0 := by omega
            have empty : group.erase source = [] := by
              cases erasedShape : group.erase source with
              | nil => rfl
              | cons c rest => simp only [erasedShape, List.length_cons] at lengthZero; omega
            have gone : update group (.push source (.fill hole)) = [] := by
              simp only [update, move, if_pos owner, post, empty]
            exact False.elim (nextSurvives (by rw [gone, endGroup_empty]))
          · simp only [ownCredit, if_neg owner]
    simp only [ownCredits, firstZero, restZero, Int.zero_add]

theorem survivor_energy (potential : Potential) (cell : Cell) (outcomes : List Outcome)
    (survives : endGroup [cell] outcomes ≠ []) :
    energy potential [cell] outcomes = -potential.boulder cell + Int.ofNat (ownPushes [cell] outcomes) := by
  have ledger := group_ledger potential [cell] outcomes
  have noCredit := survivor_credits_zero potential [cell] outcomes (by simp) survives
  rw [noCredit] at ledger
  simp only [debtOf, weightSum, Int.add_zero] at ledger
  exact ledger.symm

theorem endGroup_append (group : List Cell) (first second : List Outcome) :
    endGroup group (first ++ second) = endGroup (endGroup group first) second := by
  induction first generalizing group with
  | nil => rfl
  | cons outcome rest ih => exact ih (update group outcome)

theorem ownSlack_append (potential : Potential) (group : List Cell) (first second : List Outcome) :
    ownSlack potential group (first ++ second) =
      ownSlack potential group first + ownSlack potential (endGroup group first) second := by
  induction first generalizing group with
  | nil => simp only [List.nil_append, ownSlack, endGroup, Int.zero_add]
  | cons outcome rest ih =>
    simp only [List.cons_append, ownSlack, endGroup, ih]
    omega

#print axioms survivor_energy
#print axioms no_push_unchanged
end Owner1007.TokenAccounting
