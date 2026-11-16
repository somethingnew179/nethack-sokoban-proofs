import Owner1007.SidecarCriticalImpossible12
namespace Owner1007.SidecarCriticalFixed12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.SidecarCoreQuiet12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem credits_zero_of_preserved_length (potential : Potential) (group : List Cell) (outcomes : List Outcome)
 (same : (endGroup group outcomes).length=group.length) : ownCredits potential group outcomes=0 := by
 induction outcomes generalizing group with
 | nil => rfl
 | cons outcome rest ih =>
   have nextLe := update_length group outcome
   have finalLe := endGroup_length_le (update group outcome) rest
   change (endGroup (update group outcome) rest).length=group.length at same
   have nextSame : (update group outcome).length=group.length := by omega
   have tailSame : (endGroup (update group outcome) rest).length=(update group outcome).length := by omega
   have tailZero := ih (update group outcome) tailSame
   have headZero : ownCredit potential group outcome=0 := by
     cases outcome with
     | walk target => rfl
     | push source ending =>
       cases ending with
       | stay target => rfl
       | fill hole =>
         by_cases owner : source∈group
         · have positive := List.length_pos_of_mem owner
           have erased := List.length_erase_of_mem owner
           simp only [update,move,if_pos owner,post] at nextSame
           omega
         · simp only [ownCredit,if_neg owner]
   simp only [ownCredits,headZero,tailZero,Int.zero_add]

theorem quiet_of_zero_slack (potential : Potential) (group : List Cell) (outcomes : List Outcome)
 (same : endGroup group outcomes=group) (zero : ownSlack potential group outcomes=0) :
 ownPushes group outcomes=0 := by
 have credits := credits_zero_of_preserved_length potential group outcomes (by rw [same])
 have ledger := group_ledger potential group outcomes
 rw [same,credits,zero] at ledger
 simp only [Int.ofNat_eq_natCast] at ledger
 omega

theorem impossible
 {final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228)
 {d1 p1 m1 before middle1 t1 d2 p2 m2 between middle2 t2 d3 p3 m3 after}
 (shape : outcomes=before++.push 238 (.stay 264)::(between++.push 264 (.stay 290)::after))
 (first : Logged soko1_2.board FirstSplit12.afterN d1 middle1 p1 m1 before)
 (head1 : step soko1_2.board middle1 .south=some t1)
 (effect1 : Matches middle1 t1 (.push 238 (.stay 264)))
 (second : Logged soko1_2.board t1.state d2 middle2 p2 m2 between)
 (head2 : step soko1_2.board middle2 .south=some t2)
 (effect2 : Matches middle2 t2 (.push 264 (.stay 290)))
 (last : Logged soko1_2.board t2.state d3 final p3 m3 after)
 (tag0 : endGroup (Core 0) before=Core 0)
 (tag1 : endGroup (Core 1) between=Core 1)
 (sTag : endGroup [213] before=[211])
 (i : Fin 5) (cashLocks : AfterJ12.locks 1 i⊆
   endGroup NorthBound12.G (before++.push 238 (.stay 264)::between)) : False := by
 have gEight := (NorthTight22812.canonical_ledgers logged completed cheap).2.2.1
 change energy p NorthBound12.G outcomes=8 at gEight
 have bottom := NorthBound12.bottom_north_energy_two logged
 change 2≤energy p NorthBound12.BottomN outcomes at bottom
 have gSplit := logged.energy_split (by decide +kernel) p NorthBound12.J NorthBound12.BottomN
   (by decide +kernel) (by decide +kernel)
 change energy p NorthBound12.G outcomes=energy p NorthBound12.J outcomes+energy p NorthBound12.BottomN outcomes at gSplit
 have sameJ : (Core 0).Perm NorthBound12.J := by decide +kernel
 have jBudget : energy p (Core 0) outcomes≤6 := by rw [energy_perm p sameJ];omega
 have owner0 : (238:Cell)∈Core 0 := by decide +kernel
 have owner1 : (264:Cell)∈Core 1 := by decide +kernel
 have firstPrice : slack p (.push 238 (.stay 264))=2 := by decide +kernel
 have secondPrice : slack p (.push 264 (.stay 290))=4 := by decide +kernel
 have shift1 : (update (Core 0) (.push 238 (.stay 264))).Perm (Core 1) := by decide +kernel
 have shift2 : (update (Core 1) (.push 264 (.stay 290))).Perm (Core 2) := by decide +kernel
 have exactCore : energy p (Core 0) outcomes=
     ownSlack p (Core 0) before+2+ownSlack p (Core 1) between+4+energy p (Core 2) after := by
   rw [shape,energy_at_split,tag0]
   simp only [projectedOutcome,if_pos owner0,firstPrice]
   rw [energy_perm p shift1,energy_at_split,tag1]
   simp only [projectedOutcome,if_pos owner1,secondPrice]
   rw [energy_perm p shift2]
   omega
 have nn0 := first.ownSlack_nonnegative Generated.soko1_2_potential_valid (Core 0)
 have nn1 := second.ownSlack_nonnegative Generated.soko1_2_potential_valid (Core 1)
 have nn2 := last.energy_nonnegative Generated.soko1_2_potential_valid (Core 2)
 change 0≤ownSlack p (Core 0) before at nn0
 change 0≤ownSlack p (Core 1) between at nn1
 change 0≤energy p (Core 2) after at nn2
 have zero0 : ownSlack p (Core 0) before=0 := by omega
 have zero1 : ownSlack p (Core 1) between=0 := by omega
 have quiet0 := quiet_of_zero_slack p (Core 0) before tag0 zero0
 have quiet1 := quiet_of_zero_slack p (Core 1) between tag1 zero1
 have selected := first.end_subset (by decide +kernel) [213] (by decide +kernel) (by decide +kernel)
 have at211 : (211:Cell)∈middle1.boulders := selected.2 (by rw [sTag];simp)
 have post211 : (211:Cell)∈t1.state.boulders := by
   have kept := GhostSubset.update_subset middle1 t1 (.push 238 (.stay 264)) effect1 [211]
     (by decide +kernel) (by simpa using at211)
   have same : update [211] (.push 238 (.stay 264))=[211] := by decide +kernel
   rw [same] at kept
   exact kept (by simp)
 exact SidecarCriticalImpossible12.impossible logged completed cheap shape first head1 effect1 second
   head2 effect2 last quiet0 quiet1 post211 i cashLocks
#print axioms quiet_of_zero_slack
#print axioms impossible
end Owner1007.SidecarCriticalFixed12
