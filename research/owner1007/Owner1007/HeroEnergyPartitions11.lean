import Owner1007.Hero315Frame11
namespace Owner1007.Hero315Frame11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

theorem energy_perm {first second : List Cell} (same : first.Perm second)
    (initial final : State) (outcomes : List Outcome) :
    energy initial final first outcomes = energy initial final second outcomes := by
  have charges : HeroLedger.charges NetHack.Soko11Hero315.holeWeight first outcomes =
      HeroLedger.charges NetHack.Soko11Hero315.holeWeight second outcomes := by
    simpa only [HeroLedger.charges_eq_potential_energy] using
      TokenAccounting.energy_perm (HeroLedger.holeOnly NetHack.Soko11Hero315.holeWeight) same outcomes
  have terminal := StatePermutation.weightSum_permutation (weightAt final) (endGroup_perm same outcomes)
  have initialValue := StatePermutation.weightSum_permutation (weightAt initial) same
  unfold energy HeroLedger.energy value
  rw [charges, terminal, initialValue]

theorem energy_split {dirs final pushes moves outcomes}
    (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
    (first second : List Cell) (unique : (first ++ second).Nodup)
    (inside : first ++ second ⊆ soko1_1.initial.boulders) :
    energy soko1_1.initial final (first ++ second) outcomes =
      energy soko1_1.initial final first outcomes + energy soko1_1.initial final second outcomes :=
  HeroLedger.Logged.energy_split logged (by decide +kernel) weightAt
    NetHack.Soko11Hero315.holeWeight first second unique inside

#print axioms energy_perm
#print axioms energy_split
end Owner1007.Hero315Frame11
