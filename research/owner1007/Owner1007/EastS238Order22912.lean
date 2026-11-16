import Owner1007.EastTight22912
import Owner1007.Zero213West12
import Owner1007.Vertical21223812
namespace Owner1007.EastS238Order22912
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting Owner1007.OwnedEvents12
abbrev p := Generated.soko1_2Potential
def Selected : List Cell := EastTight22912.OtherG++[213]
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem first_west_requires_238 {beforeDirs state beforePushes beforeMoves before t
    afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_2.board EastPrice225.afterE beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_2.board state .west=some t)
 (effect : Matches state t (.push 213 (.stay 212)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (stationaryS : ownPushes [213] before=0)
 (zero : energy p Selected (before++.push 213 (.stay 212)::after)=0) :
 0<ownPushes [238] before := by
 apply Nat.pos_of_ne_zero
 intro stationary238
 have tagS := no_push_unchanged [213] before stationaryS
 have tag238 := no_push_unchanged [238] before stationary238
 have old := first.end_subset (by decide +kernel) Selected (by decide +kernel) (by decide +kernel)
 have inclS := first.member_end_subset (by decide +kernel) Selected (by decide +kernel)
   (by decide +kernel) 213 (by decide +kernel)
 have incl238 := first.member_end_subset (by decide +kernel) Selected (by decide +kernel)
   (by decide +kernel) 238 (by decide +kernel)
 rw [tagS] at inclS
 rw [tag238] at incl238
 have owner : (213:Cell)∈endGroup Selected before := inclS (by simp)
 have pair : ([213,238]:List Cell)⊆endGroup Selected before := by
   intro c member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl
   ·exact owner
   ·exact incl238 (by simp)
 have shift := CageFour12.shifted_inside (show ([213,238]:List Cell).Nodup by decide +kernel)
   pair owner (show [212,238]⊆212::([213,238]:List Cell).erase 213 by decide +kernel)
 have reached := East22612.east_reached.append first.trace
 have actual := step_boulders_nodup _ _ _ _ (reached.boulders_nodup (by decide +kernel)) head
 have nextUnique := GhostSubset.update_unique state t (.push 213 (.stay 212)) effect actual
   (endGroup Selected before) old.1 old.2
 have nextInside := GhostSubset.update_subset state t (.push 213 (.stay 212)) effect
   (endGroup Selected before) old.1 old.2
 have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
 have player := matches_hero state t (.push 213 (.stay 212)) effect
 have later := Vertical21223812.owned_energy_two last nextReached
   (update (endGroup Selected before) (.push 213 (.stay 212))) nextUnique nextInside
   (by rw [player];decide +kernel) shift
 change 2≤energy p (update (endGroup Selected before) (.push 213 (.stay 212))) after at later
 have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid Selected
 change 0≤ownSlack p Selected before at prefixNN
 have one : slack p (.push 213 (.stay 212))=0 := by decide +kernel
 rw [energy_at_split] at zero
 simp only [projectedOutcome,if_pos owner,one,Int.add_zero] at zero
 omega

/-- The original238 must move strictly before the original213's first West
push. This is extracted from every hypothetical original east-first229 trace. -/
theorem canonical {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board EastPrice225.afterE dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤229) :
 ∃ beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves,
 outcomes=before++.push 213 (.stay 212)::after ∧
 Logged soko1_2.board EastPrice225.afterE beforeDirs middle beforePushes beforeMoves before ∧
 step soko1_2.board middle .west=some t ∧Matches middle t (.push 213 (.stay 212)) ∧
 Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
 ownPushes [213] before=0 ∧0<ownPushes [238] before ∧middle.player=214 := by
 obtain ⟨_,_,zeroS,_,_,zeroG⟩ := EastTight22912.canonical_ledgers logged completed cheap
 change energy p [213] outcomes=0 at zeroS
 change energy p EastTight22912.OtherG outcomes=0 at zeroG
 have split := logged.energy_split (by decide +kernel) p EastTight22912.OtherG [213]
   (by decide +kernel) (by decide +kernel)
 have zero : energy p Selected outcomes=0 := by
   change energy p Selected outcomes=energy p EastTight22912.OtherG outcomes+energy p [213] outcomes at split
   omega
 obtain ⟨bd,bp,bm,before,middle,t,after,ad,ap,am,shape,first,head,effect,last,stationary,hero⟩ :=
   Zero213West12.first_west logged East22612.east_reached zeroS
 have moved := first_west_requires_238 first head effect last stationary (by rw [←shape];exact zero)
 exact ⟨bd,bp,bm,before,middle,t,after,ad,ap,am,shape,first,head,effect,last,stationary,moved,hero⟩
#print axioms first_west_requires_238
#print axioms canonical
end Owner1007.EastS238Order22912
