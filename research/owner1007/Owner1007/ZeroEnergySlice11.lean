import Owner1007.HeroEnergySlice11
import Owner1007.HeroEnergySubset11
namespace Owner1007.ZeroEnergySlice11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

theorem subset_zero {beforeDirs state beforePushes beforeMoves before dirs middle pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs middle pushes moves outcomes)
 (suffix : Logged soko1_1.board middle lastDirs final lastPushes lastMoves last)
 (original : List Cell) (originalUnique : original.Nodup) (originalInside : original⊆soko1_1.initial.boulders)
 (zero : energy soko1_1.initial final original (before++outcomes++last)=0)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆endGroup original before) :
 energy state middle group outcomes=0 := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have facts := first.end_subset (by decide) original originalUnique originalInside
 have originalBound := List.Nodup.length_le_of_subset originalUnique originalInside
 change original.length≤18 at originalBound
 have currentBound := Nat.le_trans (endGroup_length_le original before) originalBound
 have groupBound := Nat.le_trans (List.Nodup.length_le_of_subset unique subset) currentBound
 have inside := List.Subset.trans subset facts.2
 have compare := energy_subset first.trace logged group (endGroup original before) unique facts.1 subset facts.2 currentBound
 have slice := slice_energy_le first logged suffix original originalUnique originalInside
 have nn := HeroLedger.Logged.energy_nonnegative logged (groupCertificate 18) valid group unique inside groupBound
 change 0≤energy state middle group outcomes at nn
 omega
#print axioms subset_zero
end Owner1007.ZeroEnergySlice11
