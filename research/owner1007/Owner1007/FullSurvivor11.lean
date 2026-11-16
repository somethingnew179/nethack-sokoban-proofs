import Owner1007.HeroLedger
namespace Owner1007.TokenAccounting
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition

theorem full_survivor_credits_zero (potential : Potential) (group : List Cell) (outcomes : List Outcome)
    (same : (endGroup group outcomes).length = group.length) :
    ownCredits potential group outcomes = 0 := by
  induction outcomes generalizing group with
  | nil => rfl
  | cons outcome rest ih =>
    have bound := endGroup_length_le (update group outcome) rest
    have nextBound := update_length group outcome
    have nextSame : (update group outcome).length = group.length := by
      change (endGroup (update group outcome) rest).length = group.length at same
      omega
    have tailSame : (endGroup (update group outcome) rest).length = (update group outcome).length := by
      change (endGroup (update group outcome) rest).length = group.length at same
      omega
    have tailZero := ih (update group outcome) tailSame
    have firstZero : ownCredit potential group outcome = 0 := by
      cases outcome with
      | walk target => rfl
      | push source result =>
        cases result with
        | stay landing => rfl
        | fill hole =>
          by_cases owner : source ∈ group
          · have erased := List.length_erase_of_mem owner
            have positive := List.length_pos_of_mem owner
            simp only [update,move,if_pos owner,post] at nextSame
            omega
          · simp only [ownCredit,if_neg owner]
    simp only [ownCredits,firstZero,tailZero,Int.zero_add]
end Owner1007.TokenAccounting

namespace Owner1007.HeroLedger
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

theorem full_survivor_energy (value : State → List Cell → Int) (holeWeight : Cell → Int)
    (initial final : State) (group : List Cell) (outcomes : List Outcome)
    (same : (endGroup group outcomes).length = group.length)
    (terminal : value final (endGroup group outcomes) = 0) :
    energy value holeWeight initial final group outcomes =
      Int.ofNat (ownPushes group outcomes) - value initial group := by
  have credits := full_survivor_credits_zero (holeOnly holeWeight) group outcomes same
  have ledger := charges_eq_own holeWeight group outcomes
  unfold energy
  rw [ledger,credits,terminal]
  omega
#print axioms full_survivor_energy
end Owner1007.HeroLedger
