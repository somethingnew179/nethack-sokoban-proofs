import Owner1007.Left186TagPrice11
import Owner1007.LeftStrict11
import Owner1007.RightEarlyQuiet11
import Owner1007.UpperShaftGate11
import Owner1007.HeroEnergyTrace11
namespace Owner1007.LeftTwoLaneBad11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem no_west185 {beforeDirs state beforePushes beforeMoves before t outcome afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t outcome)
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (tag : endGroup [186] before=[185]) (metadata : t.pushSource=some 185)
 (cheap : energy soko1_1.initial final [186] (before++outcome::after)≤2) : False := by
 have prefixTwo := Left186TagPrice11.at185_two first tag
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have selected := first.end_subset (by decide) [186] (by decide) (by decide)
 have row := LeftStrict11.exit_row scalar rfl valid head effect selected.1 selected.2
  ⟨185,by rw [tag];simp,metadata,by simp [LeftActor11.Exit]⟩
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup [186] before) outcome+
  value t.state (update (endGroup [186] before) outcome)-value state (endGroup [186] before) at row
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
theorem no_north190 {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : UpperQuiet11.Quiet RightEarlyWords11.paid soko1_1.initial RightEarlyWords11.G beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .north=some t) (effect : Matches state t (.push 190 (.stay 164)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (upperCheap : energy soko1_1.initial final UpperBudget11.U6 (before++.push 190 (.stay 164)::after)<8)
 (restCheap : energy soko1_1.initial final UpperBudget11.Rest (before++.push 190 (.stay 164)::after)<2) : False := by
 have zero137 := first.fixed (show 137∈RightEarlyWords11.G by decide) (by intro d;exact Or.inl rfl)
 have zero139 := first.fixed (show 139∈RightEarlyWords11.G by decide) (by intro d;exact Or.inr (Or.inl rfl))
 have moved := UpperShaftGate11.gate_moved_before_north first.logged head effect last completed upperCheap restCheap
 omega
theorem no_east190 {beforeDirs state beforePushes beforeMoves before t}
 (first : UpperQuiet11.Quiet RightEarlyWords11.paid soko1_1.initial RightEarlyWords11.G beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .east=some t) (effect : Matches state t (.push 190 (.stay 191)))
 (owner : 190∈endGroup [186,188] before) : False := by
 obtain ⟨i,_,_,tag191,_,_,_⟩:=RightEarlyWords11.quiet_packet first
 have choices : RightEarlyWords11.q i=191∨RightEarlyWords11.q i=190 := by unfold RightEarlyWords11.q;split <;>simp
 rcases choices with same|same
 ·rw [same] at tag191
  have present191 : 191∈state.boulders := (first.logged.end_subset (by decide) [191] (by decide) (by decide)).2 (by rw [tag191];simp)
  obtain ⟨result,_,push⟩:=effect_push_data head effect
  obtain ⟨dest,next,_,_,clear⟩:=(push_first_clear _ _ _ _ _ push).2
  have destEq : dest=191 := Option.some.inj (next.symm.trans (show advance soko1_1.board 190 .east=some 191 by decide +kernel))
  exact clear (destEq.symm ▸ present191)
 ·rw [same] at tag191
  have actual := first.logged.end_subset (by decide) ([186,188]++[191]) (by decide) (by decide)
  have partition := HeroLedger.Logged.end_append_perm first.logged (by decide) [186,188] [191] (by decide) (by decide)
  have unique := partition.nodup_iff.mp actual.1
  have separate := (List.nodup_append.mp unique).2.2
  exact separate 190 owner 190 (by rw [tag191];simp) rfl
#print axioms no_west185
#print axioms no_north190
#print axioms no_east190
end Owner1007.LeftTwoLaneBad11
