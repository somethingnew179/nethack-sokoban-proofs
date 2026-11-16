import Owner1007.Left184Price11
import Owner1007.LeftTwoLaneBad11
namespace Owner1007.LeftFourLaneBad11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem no_west184 {beforeDirs state beforePushes beforeMoves before t outcome afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t outcome)
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (tag : endGroup [186] before=[184]) (metadata : t.pushSource=some 184)
 (cheap : energy soko1_1.initial final [186] (before++outcome::after)≤4) : False := by
 have prefixTwo := Left186TagPrice11.at184_three first tag
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have selected := first.end_subset (by decide) [186] (by decide) (by decide)
 have row := Left184Price11.exit_row valid head effect selected.1 selected.2
  (by rw [tag];simp) metadata
 have actual := step_boulders_nodup _ _ _ _ valid.1 head
 have nextUnique := GhostSubset.update_unique _ _ _ effect actual _ selected.1 selected.2
 have nextInside := GhostSubset.update_subset _ _ _ effect _ selected.1 selected.2
 have beforeBound := endGroup_length_le [186] before
 have nextBound := update_length (endGroup [186] before) outcome
 have nextValid := (groupCertificate 18).preserved _ _ _ valid head
 have tailNN := HeroLedger.Logged.energy_nonnegative last (groupCertificate 18) nextValid
  _ nextUnique nextInside (by simp only [List.length_singleton] at beforeBound;omega)
 change 0≤energy t.state final (update (endGroup [186] before) outcome) after at tailNN
 have split := energy_append soko1_1.initial state final [186] before (outcome::after)
 have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final (endGroup [186] before) outcome after
 change energy state final (endGroup [186] before) (outcome::after)=
  charge NetHack.Soko11Hero315.holeWeight (endGroup [186] before) outcome+
  value t.state (update (endGroup [186] before) outcome)-value state (endGroup [186] before)+
  energy t.state final (update (endGroup [186] before) outcome) after at one
 omega

#print axioms no_west184
end Owner1007.LeftFourLaneBad11
