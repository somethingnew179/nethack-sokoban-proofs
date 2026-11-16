import Owner1007.RightEntryBound12
import Owner1007.EastRightStationary12
import Owner1007.East22612
import Owner1007.Final222
import Owner1007.FirstSplit12

namespace Owner1007.East22712
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev R := RightEnergy12.Right

theorem right_five_suffix
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board EastPrice225.afterE dirs final pushes moves outcomes)
 (completed : Goal final) : 5≤energy p R outcomes := by
 have initialUnique : EastPrice225.afterE.boulders.Nodup := by decide +kernel
 rcases event_or_good EastCorral12.closed EastCorral12.unique logged East22612.east_reached East22612.G
   (by decide +kernel) (by decide +kernel) (i:=0) (by decide +kernel) (by decide +kernel) with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,i,shape,first,checked,effect,last,heroOne,locksOne,pays,fixed,zero⟩ :=
     EastRightStationary12.split_stationary event East22612.east_reached (by decide +kernel) (by decide +kernel)
   cases outcome with
   | walk target => exact False.elim pays
   | push source ending =>
     obtain ⟨owner,pays⟩ := pays
     change source=296 ∧ dir=.north at pays
     obtain ⟨rfl,rfl⟩ := pays
     have middleReached := East22612.east_reached.append first.trace
     have middleUnique := middleReached.boulders_nodup (by decide +kernel)
     have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
       (show pushTargets soko1_2.board 296 .north=[270] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     change endGroup R before=R at fixed
     change ownSlack p R before=0 at zero
     have previous := first.end_subset initialUnique R (by decide +kernel) (by decide +kernel)
     have oldRight : R⊆middle.boulders := by simpa only [fixed] using previous.2
     have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
     have nextRight := GhostSubset.update_subset middle t (.push 296 (.stay 270)) effect R
       (by decide +kernel) oldRight
     have absent : (296:Cell)∉R := by decide +kernel
     simp only [update,move,if_neg absent] at nextRight
     have shapeNext : t.state.boulders=270::middle.boulders.erase 296 := by
       simpa only [Matches] using congrArg (fun h:Transition=>h.state.boulders) effect.2
     have present : (270:Cell)∈t.state.boulders := by rw [shapeNext]; simp
     have frame : RightEntry12.locks 0⊆270::R := by decide +kernel
     have rightFrame : RightEntry12.locks 0⊆t.state.boulders :=
       List.Subset.trans frame (by intro c h; rcases List.mem_cons.mp h with rfl|h; exact present; exact nextRight h)
     have player : t.state.player=296 := matches_hero middle t (.push 296 (.stay 270)) effect
     have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
     have later := RightEntry12.right_five RightEntry12.matrix last nextReached player rightFrame completed
     change 5≤energy p R after at later
     rw [shape,energy_at_split,fixed]
     change 5≤ownSlack p R before+0+energy p R after
     omega
 · obtain ⟨i,hero,locksOne⟩ := terminal
   have finalInside := logged.end_subset initialUnique East22612.G (by decide +kernel) (by decide +kernel)
   have count := List.Nodup.length_le_of_subset (EastCorral12.unique i) (List.Subset.trans locksOne finalInside.2)
   rw [EastCorral12.sizes i] at count
   have two := RightEntryCapacity12.final_two logged East22612.east_reached completed
   rw [two] at count
   omega

theorem initial_right_energy (outcomes : List Outcome) :
 energy p R (.walk 370::.push 371 (.stay 372)::outcomes)=energy p R outcomes := by
 rw [energy_cons]
 simp only [projectedOutcome,slack,update,Int.zero_add]
 rw [energy_cons]
 have absent : (371:Cell)∉R := by decide +kernel
 simp only [projectedOutcome,if_neg absent,slack,update,move,Int.zero_add]

theorem east_branch_logged_227
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board EastPrice225.afterE dirs final pushes moves outcomes)
 (completed : Goal final) : 227≤1+pushes := by
 have stone := East22612.stone_six logged completed
 have rightFive := right_five_suffix logged completed
 have whole := East22612.canonical_east logged
 let all := .walk 370::.push 371 (.stay 372)::outcomes
 have stoneEight : (8:Int)≤energy p [371] all := by
   dsimp [all]
   rw [East22612.initial_stone_energy]
   exact Int.add_le_add_left stone 2
 have right : (5:Int)≤energy p Final222.R all := by
   change 5≤energy p R all
   dsimp [all]
   rw [initial_right_energy]
   exact rightFive
 have mono := whole.member_energy_le Generated.soko1_2_potential_valid (by decide +kernel)
   Final222.G (by decide +kernel) (by decide +kernel) 371 (by decide +kernel)
 change energy p [371] all≤energy p Final222.G all at mono
 have upper := Final222.upper_energy_two whole completed
 change 2≤energy p Final222.U all at upper
 have other := whole.energy_nonnegative Generated.soko1_2_potential_valid [213]
 change 0≤energy p [213] all at other
 have total := Final222.total_energy whole completed
 change energy p Final222.U all+energy p Final222.G all+energy p [213] all+energy p Final222.R all=
   Int.ofNat (1+pushes)-212 at total
 simp only [Int.ofNat_eq_natCast] at total
 omega

theorem east_branch_227
 {dirs final pushes moves}
 (trace : Trace soko1_2.board FirstSplit12.afterE dirs final pushes moves)
 (completed : Goal final) : 227≤1+pushes := by
 obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
 exact east_branch_logged_227 logged completed
#print axioms east_branch_227
end Owner1007.East22712

