import Owner1007.TokenPersistence
import NetHack.Sokoban.GhostScalar

namespace Owner1007.HeroLedger
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

/-- Charge of one persistent group, including its own consumed-hole credits. -/
def charges (holeWeight : Cell → Int) (group : List Cell) : List Outcome → Int
  | [] => 0
  | outcome :: rest => charge holeWeight group outcome + charges holeWeight (update group outcome) rest

def energy (value : State → List Cell → Int) (holeWeight : Cell → Int)
    (initial final : State) (group : List Cell) (outcomes : List Outcome) : Int :=
  charges holeWeight group outcomes + value final (endGroup group outcomes) - value initial group

/-- The generic certificate applies to an individual persistent group.
It includes player-component and phase changes, rather than only actor prices. -/
theorem Logged.group_bound {board limit invariant initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (cert : GroupCertificate board limit invariant) (good : invariant initial)
    (group : List Cell) (unique : group.Nodup) (inside : group ⊆ initial.boulders)
    (bounded : group.length ≤ limit) :
    cert.groupValue initial group ≤ charges cert.holeWeight group outcomes +
      cert.groupValue final (endGroup group outcomes) := by
  induction logged generalizing group with
  | nil => simp only [charges, endGroup, Int.zero_add]; exact Int.le_refl _
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have one := cert.row state dir t outcome group good unique inside bounded head effect
    have nextGood := cert.preserved state dir t good head
    have nextUnique := step_boulders_nodup _ _ _ _ (cert.unique state good) head
    have selectedUnique := GhostSubset.update_unique _ _ _ effect nextUnique group unique inside
    have selectedInside := GhostSubset.update_subset _ _ _ effect group unique inside
    have selectedBound := Nat.le_trans (update_length group outcome) bounded
    have later := ih nextGood (update group outcome) selectedUnique selectedInside selectedBound
    change cert.groupValue state group ≤ _ + _
    simp only [charges, endGroup]
    omega

theorem Logged.energy_nonnegative {board limit invariant initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (cert : GroupCertificate board limit invariant) (good : invariant initial)
    (group : List Cell) (unique : group.Nodup) (inside : group ⊆ initial.boulders)
    (bounded : group.length ≤ limit) :
    0 ≤ energy cert.groupValue cert.holeWeight initial final group outcomes := by
  have bound := Logged.group_bound logged cert good group unique inside bounded
  unfold energy
  omega

def holeOnly (holeWeight : Cell → Int) : Potential :=
  {boulder := fun _ => 0, hole := holeWeight}

theorem charges_eq_own (holeWeight : Cell → Int) (group : List Cell) (outcomes : List Outcome) :
    charges holeWeight group outcomes = Int.ofNat (ownPushes group outcomes) -
      ownCredits (holeOnly holeWeight) group outcomes := by
  induction outcomes generalizing group with
  | nil => simp [charges, ownPushes, ownCredits]
  | cons outcome rest ih =>
    have tail := ih (update group outcome)
    have one : charge holeWeight group outcome = Int.ofNat (ownPush group outcome) -
        ownCredit (holeOnly holeWeight) group outcome := by
      cases outcome with
      | walk _ => rfl
      | push source result =>
        cases result <;> by_cases owner : source ∈ group <;>
          simp [charge, ownPush, ownCredit, holeOnly, owner]
    simp only [charges, ownPushes, ownCredits, Int.ofNat_eq_natCast, Int.natCast_add] at *
    omega

/-- A surviving singleton has no consumed-hole charge, for any hero-dependent value. -/
theorem survivor_energy (value : State → List Cell → Int) (holeWeight : Cell → Int)
    (initial final : State) (cell : Cell) (outcomes : List Outcome)
    (survives : endGroup [cell] outcomes ≠ [])
    (terminal : value final (endGroup [cell] outcomes) = 0) :
    energy value holeWeight initial final [cell] outcomes =
      Int.ofNat (ownPushes [cell] outcomes) - value initial [cell] := by
  have credits := survivor_credits_zero (holeOnly holeWeight) [cell] outcomes (by simp) survives
  have accounting := charges_eq_own holeWeight [cell] outcomes
  unfold energy
  rw [accounting, credits, terminal]
  omega

#print axioms Logged.group_bound
#print axioms Logged.energy_nonnegative
#print axioms survivor_energy
end Owner1007.HeroLedger
