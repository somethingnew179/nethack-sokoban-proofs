import Owner1007.HeroEnergyTrace11
import Owner1007.LoggedAppend11
namespace Owner1007.Hero315Frame11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

theorem slice_energy_le {beforeDirs state beforePushes beforeMoves before dirs middle pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs middle pushes moves outcomes)
 (suffix : Logged soko1_1.board middle lastDirs final lastPushes lastMoves last)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆soko1_1.initial.boulders) :
 energy state middle (endGroup group before) outcomes≤
 energy soko1_1.initial final group (before++outcomes++last) := by
 have beforeNN := energy_nonnegative first group unique inside
 let toMiddle := first.append logged
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant toMiddle.trace
 have selected := toMiddle.end_subset (by decide) group unique inside
 have bound := Nat.le_trans (endGroup_length_le group (before++outcomes)) (List.Nodup.length_le_of_subset unique inside)
 have tailNN := HeroLedger.Logged.energy_nonnegative suffix (groupCertificate 18)
   valid (endGroup group (before++outcomes)) selected.1 selected.2 bound
 change 0≤energy middle final (endGroup group (before++outcomes)) last at tailNN
 have one := energy_append soko1_1.initial state final group before (outcomes++last)
 have two := energy_append state middle final (endGroup group before) outcomes last
 rw [endGroup_append] at tailNN
 rw [List.append_assoc]
 omega
#print axioms slice_energy_le
end Owner1007.Hero315Frame11
