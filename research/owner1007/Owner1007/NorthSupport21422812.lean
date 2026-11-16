import Owner1007.NorthUpperRigidity22812
import Owner1007.Zero213West12
namespace Owner1007.NorthSupport21422812
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
abbrev p := Generated.soko1_2Potential
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- Original P228 completions must support original187 from214 for its213West push. -/
theorem canonical_support214 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228) :
 ∃ beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves,
 outcomes=before++.push 213 (.stay 212)::after ∧
 Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before ∧
 step soko1_2.board middle .west=some t ∧Matches middle t (.push 213 (.stay 212)) ∧
 Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
 endGroup [187] before=[213] ∧middle.player=214 := by
 obtain ⟨upper,zero187⟩ := NorthUpperRigidity22812.canonical_upper_two_and_187_zero logged completed cheap
 change energy p PreCage12.U outcomes=2 at upper
 obtain ⟨bd,bp,bm,before,middle,t,after,ad,ap,am,shape,first,checked,effect,last,stationary,_⟩ :=
   Upper187ForcedSouth12.forced_south logged (by change energy p PreCage12.U outcomes≤2;omega)
 have tag := no_push_unchanged [187] before stationary
 have split : energy p [187] outcomes=ownSlack p [187] before+energy p [213] after := by
   rw [shape,energy_at_split,tag]
   have headZero : slack p (.push 187 (.stay 213))=0 := by decide +kernel
   simp only [projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true,headZero,Int.add_zero]
   rfl
 have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid [187]
 change 0≤ownSlack p [187] before at nn
 have laterNN := last.energy_nonnegative Generated.soko1_2_potential_valid [213]
 change 0≤energy p [213] after at laterNN
 change energy p [187] outcomes=0 at zero187
 have zero213 : energy p [213] after=0 := by omega
 have reached := (NorthBound12.north_reached.append first.trace).append (Trace.cons checked (Trace.nil t.state))
 obtain ⟨bd2,bp2,bm2,before2,middle2,t2,after2,ad2,ap2,am2,shape2,first2,checked2,effect2,last2,stationary2,hero2⟩ :=
   Zero213West12.first_west last reached zero213
 let combined := before++.push 187 (.stay 213)::before2
 let prefixLogged := first.append (Logged.cons checked effect first2)
 have allShape : outcomes=combined++.push 213 (.stay 212)::after2 := by
   rw [shape,shape2]
   simp only [combined,List.append_assoc,List.cons_append]
 have originalTag : endGroup [187] combined=[213] := by
   unfold combined
   rw [endGroup_append,tag]
   change endGroup [213] before2=[213]
   exact no_push_unchanged [213] before2 stationary2
 exact ⟨_,_,_,combined,middle2,t2,after2,ad2,ap2,am2,allShape,prefixLogged,
   checked2,effect2,last2,originalTag,hero2⟩
#print axioms canonical_support214
end Owner1007.NorthSupport21422812
