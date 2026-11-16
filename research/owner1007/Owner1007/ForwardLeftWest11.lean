import Owner1007.LeftStrict11
import Owner1007.UpperLocalPrice11
import Owner1007.HeroEnergyTrace11
namespace Owner1007.ForwardLeftWest11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem four {beforeDirs state beforePushes beforeMoves before source t outcome afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t outcome)
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (tag : endGroup [186] before=[source]) (metadata : t.pushSource=some source)
 (sources : source∈([185,186,187] : List Cell))
 (prefixTwo : 2≤energy soko1_1.initial state [186] before) :
 4≤energy soko1_1.initial final [186] (before++outcome::after) := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have selected := first.end_subset (by decide) [186] (by decide) (by decide)
 have owner : source∈endGroup [186] before := by rw [tag];simp
 have row : 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup [186] before) outcome+
  value t.state (update (endGroup [186] before) outcome)-value state (endGroup [186] before) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at sources
  rcases sources with rfl|rfl|rfl
  ·exact LeftStrict11.exit_row scalar rfl valid head effect selected.1 selected.2
    ⟨185,owner,metadata,by simp [LeftActor11.Exit]⟩
  ·exact LeftStrict11.exit_row scalar rfl valid head effect selected.1 selected.2
    ⟨186,owner,metadata,by simp [LeftActor11.Exit]⟩
  ·exact UpperLocalPrice11.exit_row valid selected.1 selected.2 head effect
    ⟨187,owner,metadata,by simp [UpperLocalPrice11.paid,UpperLocalPrice11.westSources]⟩
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

#print axioms four
end Owner1007.ForwardLeftWest11
