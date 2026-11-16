import Owner1007.Lower291OwnedActivation12
namespace Owner1007.Lower291ThreeHeads12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def kind (k : Fin 3) : Fin 2 := if k.val=0 then 0 else 1
def firstSource (k : Fin 3) : Cell := if k.val=2 then 238 else 210
def firstDest (k : Fin 3) : Cell := if k.val=2 then 264 else 236
def secondSource (k : Fin 3) : Cell := if k.val=0 then 236 else if k.val=1 then 238 else 210
def secondDest (k : Fin 3) : Cell := if k.val=0 then 262 else if k.val=1 then 264 else 236
def A (k : Fin 3) : Outcome := .push (firstSource k) (.stay (firstDest k))
def B (k : Fin 3) : Outcome := .push (secondSource k) (.stay (secondDest k))
def C1 (k : Fin 3) : List Cell := if k.val=2 then AfterJ12.ordinary 1 else AfterJ12.ordinary 0
def C2 (k : Fin 3) : List Cell := Lower291OwnedActivation12.ordinary (kind k)
theorem data : ∀ k,
 firstSource k∈NorthBound12.J ∧secondSource k∈C1 k ∧
 slack p (A k)=2 ∧slack p (B k)=2 ∧
 (update NorthBound12.J (A k)).Perm (C1 k) ∧(update (C1 k) (B k)).Perm (C2 k) := by decide +kernel

theorem impossible
 {final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228) (k : Fin 3)
 {d1 p1 m1 o1 s1 t1 d2 p2 m2 o2 s2 t2 d3 p3 m3 o3 s3 t3 d4 p4 m4 after}
 (shape : outcomes=o1++A k::(o2++B k::(o3++.push 265 (.stay 291)::after)))
 (first1 : Logged soko1_2.board FirstSplit12.afterN d1 s1 p1 m1 o1)
 (head1 : step soko1_2.board s1 .south=some t1) (effect1 : Matches s1 t1 (A k))
 (first2 : Logged soko1_2.board t1.state d2 s2 p2 m2 o2)
 (head2 : step soko1_2.board s2 .south=some t2) (effect2 : Matches s2 t2 (B k))
 (first3 : Logged soko1_2.board t2.state d3 s3 p3 m3 o3)
 (head3 : step soko1_2.board s3 .south=some t3) (effect3 : Matches s3 t3 (.push 265 (.stay 291)))
 (last : Logged soko1_2.board t3.state d4 final p4 m4 after)
 (tag0 : endGroup NorthBound12.J o1=NorthBound12.J)
 (tag1 : endGroup (C1 k) o2=C1 k)
 (tag2 : endGroup (C2 k) o3=C2 k)
 (j : Fin 5)
 (inside : Lower291OwnedActivation12.locks (kind k) j⊆endGroup NorthBound12.G
   (o1++A k::(o2++B k::o3))) :False := by
 obtain ⟨owner1,owner2,price1,price2,shift1,shift2⟩ := data k
 let before := o1++A k::(o2++B k::o3)
 let first := first1.append (Logged.cons head1 effect1
   (first2.append (Logged.cons head2 effect2 first3)))
 have allShape : outcomes=before++.push 265 (.stay 291)::after := by
   rw [shape]
   simp only [before,List.append_assoc,List.cons_append]
 have own1 : projectedOutcome NorthBound12.J (A k)=A k := by
   unfold A
   simp only [projectedOutcome,if_pos owner1]
 have own2 : projectedOutcome (C1 k) (B k)=B k := by
   unfold B
   simp only [projectedOutcome,if_pos owner2]
 have nn1 := first1.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthBound12.J
 have nn2 := first2.ownSlack_nonnegative Generated.soko1_2_potential_valid (C1 k)
 have nn3 := first3.ownSlack_nonnegative Generated.soko1_2_potential_valid (C2 k)
 change 0≤ownSlack p NorthBound12.J o1 at nn1
 change 0≤ownSlack p (C1 k) o2 at nn2
 change 0≤ownSlack p (C2 k) o3 at nn3
 have ledger : ownSlack p NorthBound12.J before=
     ownSlack p NorthBound12.J o1+2+ownSlack p (C1 k) o2+2+ownSlack p (C2 k) o3 := by
   unfold before
   rw [ownSlack_append p NorthBound12.J o1 (A k::(o2++B k::o3)),tag0]
   simp only [ownSlack,own1,price1]
   rw [ownSlack_perm p shift1 (o2++B k::o3)]
   rw [ownSlack_append p (C1 k) o2 (B k::o3),tag1]
   simp only [ownSlack,own2,price2]
   rw [ownSlack_perm p shift2 o3]
   omega
 have paid : 4≤ownSlack p NorthBound12.J before := by omega
 have tagCore : (endGroup NorthBound12.J before).Perm (C2 k) := by
   unfold before
   rw [endGroup_append NorthBound12.J o1 (A k::(o2++B k::o3)),tag0]
   change (endGroup (update NorthBound12.J (A k)) (o2++B k::o3)).Perm (C2 k)
   apply (endGroup_perm shift1 (o2++B k::o3)).trans
   rw [endGroup_append (C1 k) o2 (B k::o3),tag1]
   change (endGroup (update (C1 k) (B k)) o3).Perm (C2 k)
   have transport := endGroup_perm shift2 o3
   rw [tag2] at transport
   exact transport
 exact Lower291OwnedActivation12.impossible logged completed cheap allShape first head3 effect3 last
   paid (kind k) j tagCore inside
#print axioms impossible
end Owner1007.Lower291ThreeHeads12
