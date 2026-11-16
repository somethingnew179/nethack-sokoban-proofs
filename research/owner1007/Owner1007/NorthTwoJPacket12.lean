import Owner1007.NorthFirstJ22812
import Owner1007.Lower291ThreeHeads12
namespace Owner1007.NorthTwoJPacket12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.Lower291ThreeHeads12 (A B C1 C2 kind secondSource secondDest)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def firstKind (k : Fin 3) : Fin 2 := if k.val=2 then 1 else 0
theorem first_data : ∀k,AfterJBound12.headOutcome (firstKind k)=A k ∧
 AfterJ12.ordinary (firstKind k)=C1 k := by decide +kernel
theorem second_inside : ∀k j,secondSource k∈AfterJ12.locks (firstKind k) j := by decide +kernel
theorem activation : ∀k j,Lower291OwnedActivation12.locks (kind k) j⊆
 secondDest k::(AfterJ12.locks (firstKind k) j).erase (secondSource k) := by decide +kernel
def afterRegion (k : Fin 3) (j : Fin 5) : List Cell :=
 if (kind k).val=0 then After21023612.region j else After23821012.region j
theorem afterHero : ∀k j,secondSource k∈afterRegion k j := by decide +kernel

/-- One of the three actual two-J-head paths. No energy or coverage premise
is hidden in this packet; canonical extraction is a separate theorem. -/
structure SecondJ {final outcomes} (first : NorthFirstJ22812.FirstJ final outcomes) where
 path : Fin 3
 firstKindEq : first.kind=firstKind path
 middle : State
 actor : Transition
 betweenDirs : List Dir
 betweenPushes : Nat
 betweenMoves : Nat
 between : List Outcome
 afterDirs : List Dir
 afterPushes : Nat
 afterMoves : Nat
 after : List Outcome
 phase : Fin 5
 shape : first.after=between++B path::after
 gap : Logged soko1_2.board first.actor.state betweenDirs middle betweenPushes betweenMoves between
 checked : step soko1_2.board middle .south=some actor
 effect : Matches middle actor (B path)
 last : Logged soko1_2.board actor.state afterDirs final afterPushes afterMoves after
 locks : AfterJ12.locks first.kind phase⊆
   endGroup (update (endGroup NorthBound12.G first.before) (AfterJBound12.headOutcome first.kind)) between
 fixedBefore : endGroup (C1 path) between=C1 path

def SecondJ.prefixOutcomes {final outcomes first} (cut : @SecondJ final outcomes first) : List Outcome :=
 first.before++A cut.path::(cut.between++[B cut.path])

theorem SecondJ.first_effect {final outcomes first} (cut : @SecondJ final outcomes first) :
 Matches first.middle first.actor (A cut.path) := by
 have eq : AfterJBound12.headOutcome first.kind=A cut.path := by rw [cut.firstKindEq];exact (first_data cut.path).1
 simpa only [eq] using first.effect

theorem SecondJ.prefix_log {final outcomes first} (cut : @SecondJ final outcomes first) :
 ∃ds pp mm,Logged soko1_2.board FirstSplit12.afterN ds cut.actor.state pp mm cut.prefixOutcomes := by
 exact ⟨_,_,_,first.first.append (.cons first.checked cut.first_effect
   (cut.gap.append (.cons cut.checked cut.effect (.nil _))))⟩

theorem SecondJ.prefix_paid {final outcomes first} (cut : @SecondJ final outcomes first) :
 4≤ownSlack p NorthBound12.J cut.prefixOutcomes := by
 obtain ⟨owner1,owner2,price1,price2,shift1,shift2⟩ := Lower291ThreeHeads12.data cut.path
 have tag0 := first.fixedBefore NorthBound12.J (by decide +kernel)
 have own1 : projectedOutcome NorthBound12.J (A cut.path)=A cut.path := by
   unfold A
   simp only [projectedOutcome,if_pos owner1]
 have own2 : projectedOutcome (C1 cut.path) (B cut.path)=B cut.path := by
   unfold B
   simp only [projectedOutcome,if_pos owner2]
 have nn1 := first.first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthBound12.J
 have nn2 := cut.gap.ownSlack_nonnegative Generated.soko1_2_potential_valid (C1 cut.path)
 change 0≤ownSlack p NorthBound12.J first.before at nn1
 change 0≤ownSlack p (C1 cut.path) cut.between at nn2
 have ledger : ownSlack p NorthBound12.J cut.prefixOutcomes=
     ownSlack p NorthBound12.J first.before+2+ownSlack p (C1 cut.path) cut.between+2 := by
   unfold SecondJ.prefixOutcomes
   rw [ownSlack_append p NorthBound12.J first.before,tag0]
   simp only [ownSlack,own1,price1]
   rw [ownSlack_perm p shift1 (cut.between++[B cut.path])]
   rw [ownSlack_append p (C1 cut.path) cut.between,cut.fixedBefore]
   simp only [ownSlack,own2,price2,Int.add_zero]
   omega
 omega

theorem SecondJ.j_tag {final outcomes first} (cut : @SecondJ final outcomes first) :
 (endGroup NorthBound12.J cut.prefixOutcomes).Perm (C2 cut.path) := by
 obtain ⟨_,_,_,_,shift1,shift2⟩ := Lower291ThreeHeads12.data cut.path
 have tag0 := first.fixedBefore NorthBound12.J (by decide +kernel)
 unfold SecondJ.prefixOutcomes
 rw [endGroup_append NorthBound12.J first.before,tag0]
 change (endGroup (update NorthBound12.J (A cut.path)) (cut.between++[B cut.path])).Perm (C2 cut.path)
 apply (endGroup_perm shift1 (cut.between++[B cut.path])).trans
 rw [endGroup_append (C1 cut.path) cut.between,cut.fixedBefore]
 exact shift2

theorem SecondJ.post_locks {final outcomes first} (cut : @SecondJ final outcomes first) :
 Lower291OwnedActivation12.locks (kind cut.path) cut.phase⊆
   endGroup NorthBound12.G cut.prefixOutcomes := by
 have pre := cut.locks
 have eq : AfterJBound12.headOutcome first.kind=A cut.path := by rw [cut.firstKindEq];exact (first_data cut.path).1
 have preOwn : secondSource cut.path∈
     endGroup (update (endGroup NorthBound12.G first.before) (AfterJBound12.headOutcome first.kind)) cut.between := by
   apply pre
   rw [cut.firstKindEq]
   exact second_inside cut.path cut.phase
 have kept := CageFour12.shifted_inside (AfterJ12.unique first.kind cut.phase) pre preOwn
   (by simpa only [cut.firstKindEq] using activation cut.path cut.phase)
 unfold SecondJ.prefixOutcomes
 rw [endGroup_append NorthBound12.G first.before]
 change Lower291OwnedActivation12.locks (kind cut.path) cut.phase⊆
   endGroup (update (endGroup NorthBound12.G first.before) (A cut.path)) (cut.between++[B cut.path])
 rw [endGroup_append]
 simpa only [eq,endGroup,Lower291ThreeHeads12.B] using kept

theorem SecondJ.post_hero {final outcomes first} (cut : @SecondJ final outcomes first) :
 cut.actor.state.player∈afterRegion cut.path cut.phase := by
 rw [matches_hero cut.middle cut.actor (B cut.path) cut.effect]
 exact afterHero cut.path cut.phase
#print axioms first_data
#print axioms SecondJ.prefix_paid
#print axioms SecondJ.j_tag
#print axioms SecondJ.post_locks
#print axioms SecondJ.post_hero
end Owner1007.NorthTwoJPacket12
