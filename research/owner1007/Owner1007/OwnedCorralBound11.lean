import Owner1007.OwnedCorral11
import Owner1007.FullSurvivor11

namespace Owner1007.OwnedCorral11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Corral11 Owner1007.PricedCorral11

theorem energy_bound {n k : Nat} {board : Board} {holes : List Cell}
    {locks region : Fin n → List Cell} {paid : Cell → Dir → Prop}
    (closed : ClosedExcept board holes locks region paid)
    (unique : ∀ i, (locks i).Nodup) (size : ∀ i, (locks i).length = k)
    {invariant : State → Prop} (cert : GroupCertificate board k invariant) (price : Int)
    (priced : ∀ state dir t outcome group,
      invariant state → group.Nodup → group ⊆ state.boulders → group.length ≤ k →
      step board state dir = some t → Matches state t outcome → PaidStep paid group dir t →
      price ≤ charge cert.holeWeight group outcome +
        cert.groupValue t.state (update group outcome) - cert.groupValue state group)
    {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
    (logged : Logged board state dirs final pushes moves outcomes)
    (valid : invariant state) (group : List Cell) (groupUnique : group.Nodup)
    (groupInside : group ⊆ state.boulders) (groupSize : group.length = k)
    (good : Good locks region state group) (holesInside : state.holes ⊆ holes)
    (debt : cert.groupValue state group ≤ -price)
    (terminal : cert.groupValue final (endGroup group outcomes) = 0) :
    price ≤ HeroLedger.energy cert.groupValue cert.holeWeight state final group outcomes := by
  by_cases negated : price ≤ HeroLedger.energy cert.groupValue cert.holeWeight state final group outcomes
  · exact negated
  · have cheap : HeroLedger.energy cert.groupValue cert.holeWeight state final group outcomes < price := by omega
    have persists := small_energy_good closed unique size cert price priced logged valid group groupUnique
      groupInside (by omega) good holesInside cheap
    obtain ⟨i,_,subset⟩ := persists
    have lower := List.Nodup.length_le_of_subset (unique i) subset
    have upper := endGroup_length_le group outcomes
    have same : (endGroup group outcomes).length = group.length := by rw [size i] at lower; omega
    have paid := HeroLedger.full_survivor_energy cert.groupValue cert.holeWeight state final group outcomes same terminal
    have nonnegative : (0 : Int) ≤ Int.ofNat (ownPushes group outcomes) := Int.ofNat_nonneg _
    omega
#print axioms energy_bound
end Owner1007.OwnedCorral11
