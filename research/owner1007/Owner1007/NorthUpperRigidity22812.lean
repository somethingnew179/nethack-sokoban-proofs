import Owner1007.NorthSNecessary22812
import Owner1007.North211Tight22812
import Owner1007.Upper187ForcedSouth12
namespace Owner1007.NorthUpperRigidity22812
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.PreCage12
open Owner1007.NorthTagFacts12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem canonical_upper_two_and_187_zero {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228) :
 energy p U outcomes=2 ∧energy p [187] outcomes=0 := by
 obtain ⟨bd,bp,bm,before,middle,t,after,ad,ap,am,i,shape,first,checked,effect,last,hero,locks,sAt,tAt,unchanged⟩ :=
   NorthSNecessary22812.necessary_first_s logged completed cheap
 have reached := NorthBound12.north_reached.append first.trace
 have physical := first.end_subset (by decide +kernel) selected (by decide +kernel) (by decide +kernel)
 obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
 have at212 : northS i=212 := by
   rcases NorthActivation12.pre_s_heads i middle.player hero .west (Geometry.all_directions .west)
     212 (by decide +kernel) (by decide +kernel) adjacent with blocked|actual
   · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locks physical.2) checked effect blocked)
   · exact actual.2.2
 have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 let before1 : List Outcome := before++[.push 212 (.stay 211)]
 have lead1 := first.append (Logged.cons checked effect (Logged.nil t.state))
 have shape1 : outcomes=before1++after := by
   rw [shape]
   simp only [before1,List.append_assoc,List.cons_append,List.nil_append]
 have oldG := NorthPrepared12.g_end_subset first i tAt unchanged
 have gsUnique : NorthActivation12.GS.Nodup := by decide +kernel
 have gsSubset : NorthActivation12.GS⊆FirstSplit12.afterN.boulders := by decide +kernel
 have split := first.end_split initialUnique NorthBound12.G [213] gsUnique gsSubset
 change (endGroup NorthBound12.G before++endGroup [213] before).Perm
   (endGroup NorthActivation12.GS before) at split
 rw [sAt] at split
 have preInside : NorthEvents12.locks (NorthPrepared12.oldIndex i)++[212]⊆
     endGroup NorthActivation12.GS before := by
   intro c found
   apply split.mem_iff.mp
   rcases List.mem_append.mp found with old|same
   · exact List.mem_append_left _ (oldG old)
   · exact List.mem_append_right _ same
 have ownerGS : 212∈endGroup NorthActivation12.GS before :=
   preInside (List.mem_append_right _ (by simp))
 have preUnique : (NorthEvents12.locks (NorthPrepared12.oldIndex i)++[212]).Nodup := by
   have all : ∀ j, (NorthEvents12.locks j++[212]).Nodup := by decide +kernel
   exact all _
 have shift : North21112.locks (NorthPrepared12.oldIndex i)⊆
     211::(NorthEvents12.locks (NorthPrepared12.oldIndex i)++[212]).erase 212 := by
   have all : ∀ j, North21112.locks j⊆211::(NorthEvents12.locks j++[212]).erase 212 := by decide +kernel
   exact all _
 have kept := CageFour12.shifted_inside preUnique preInside ownerGS shift
 have inside1 : North21112.locks (NorthPrepared12.oldIndex i)⊆endGroup NorthActivation12.GS before1 := by
   simpa only [before1,endGroup_append,endGroup] using kept
 have s1 : endGroup [213] before1=[211] := by
   rw [show before1=before++[.push 212 (.stay 211)] from rfl,endGroup_append,sAt]
   decide +kernel
 have fixed1 : ∀ small : List Cell, small⊆NorthEvents12.J → endGroup small before1=small := by
   intro small h
   rw [show before1=before++[.push 212 (.stay 211)] from rfl,endGroup_append,
     unchanged small (List.Subset.trans h (by decide +kernel))]
   have absent : (212:Cell)∉small := fun found=>(show (212:Cell)∉NorthEvents12.J by decide +kernel) (h found)
   simp only [endGroup,update,move,if_neg absent]
 have priced1 : 2≤ownSlack p [213] before1 := by
   have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid [213]
   change 0≤ownSlack p [213] before at nn
   rw [show before1=before++[.push 212 (.stay 211)] from rfl,ownSlack_append,sAt]
   have one : ownSlack p [212] [.push 212 (.stay 211)]=2 := by decide +kernel
   rw [one]
   omega
 have hero1 : t.state.player∈North21112.region (NorthPrepared12.oldIndex i) := by
   rw [matches_hero middle t (.push 212 (.stay 211)) effect]
   exact (North21112.start_activation i at212).2
 have upper := North211Tight22812.upper_two logged completed cheap shape1 lead1 last
   (NorthPrepared12.oldIndex i) hero1 inside1 s1 fixed1 priced1
 change energy p U outcomes=2 at upper
 obtain ⟨bd2,bp2,bm2,before2,mid2,t2,after2,ad2,ap2,am2,shape2,first2,checked2,effect2,last2,stationary2,zero⟩ :=
   Upper187ForcedSouth12.forced_south logged (by change energy p U outcomes≤2;omega)
 change energy p [187] outcomes=0 at zero
 exact ⟨upper,zero⟩
#print axioms canonical_upper_two_and_187_zero
end Owner1007.NorthUpperRigidity22812
