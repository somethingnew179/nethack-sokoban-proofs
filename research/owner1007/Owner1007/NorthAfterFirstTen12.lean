import Owner1007.TwoJPriceEleven12
import Owner1007.NorthTwoJPacket12
import Owner1007.NorthJCashTen12
import Owner1007.NorthFirstJPark23112
import Owner1007.SidecarCutEleven12
namespace Owner1007.NorthAfterFirstTen12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.NorthTwoJPacket12
open Owner1007.Lower291ThreeHeads12 (A B C1 C2 kind secondSource secondDest)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem targets : ∀k,pushTargets soko1_2.board (secondSource k) .south=[secondDest k] := by decide +kernel
theorem clear : ∀k,secondDest k∉soko1_2.initial.holes := by decide +kernel
theorem first_one : AfterJBound12.headOutcome 1=.push 238 (.stay 264) := rfl
/-- The remaining critical head is kept as an explicit actual trace packet. -/
structure Critical264 {final outcomes} (cut : NorthFirstJ22812.FirstJ final outcomes) where
 kindEq : cut.kind=1
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
 shape : cut.after=between++.push 264 (.stay 290)::after
 gap : Logged soko1_2.board cut.actor.state betweenDirs middle betweenPushes betweenMoves between
 checked : step soko1_2.board middle .south=some actor
 effect : Matches middle actor (.push 264 (.stay 290))
 last : Logged soko1_2.board actor.state afterDirs final afterPushes afterMoves after
 locks : AfterJ12.locks cut.kind phase⊆endGroup (update (endGroup NorthBound12.G cut.before) (AfterJBound12.headOutcome cut.kind)) between
 fixedBefore : ∀small : List Cell,small⊆AfterJ12.fixed cut.kind→endGroup small between=small
theorem after_first {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤230) (gBudget : energy p NorthBound12.G outcomes≤10)
 (cut : NorthFirstJ22812.FirstJ final outcomes) : Nonempty (SecondJ cut)∨Nonempty (Critical264 cut) := by
 let group := update (endGroup NorthBound12.G cut.before) (AfterJBound12.headOutcome cut.kind)
 have beforeReached := NorthBound12.north_reached.append cut.first.trace
 have beforeActual := beforeReached.boulders_nodup (by decide +kernel)
 have selected := cut.first.end_subset (by decide +kernel) NorthBound12.G (by decide +kernel) (by decide +kernel)
 have actual := step_boulders_nodup _ _ _ _ beforeActual cut.checked
 have gUnique := GhostSubset.update_unique _ _ _ cut.effect actual _ selected.1 selected.2
 have gSubset := GhostSubset.update_subset _ _ _ cut.effect _ selected.1 selected.2
 have reached := beforeReached.append (Trace.cons cut.checked (Trace.nil cut.actor.state))
 have firstOwner : AfterJBound12.startSource cut.kind∈endGroup NorthBound12.G cut.before :=
   cut.locks (AfterJBound12.source_inside cut.kind cut.phase)
 have ten:=gBudget
 have prefixNN := cut.first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthBound12.G
 change 0≤ownSlack p NorthBound12.G cut.before at prefixNN
 have ledger : energy p NorthBound12.G outcomes=ownSlack p NorthBound12.G cut.before+2+energy p group cut.after := by
   have expanded := (congrArg (energy p NorthBound12.G) cut.shape).trans
     (energy_at_split p NorthBound12.G cut.before (AfterJBound12.headOutcome cut.kind) cut.after)
   simp only [AfterJBound12.headOutcome,projectedOutcome,if_pos firstOwner] at expanded
   change energy p NorthBound12.G outcomes=ownSlack p NorthBound12.G cut.before+
     slack p (AfterJBound12.headOutcome cut.kind)+energy p group cut.after at expanded
   rw [AfterJBound12.first_price] at expanded
   exact expanded
 have budget : energy p group cut.after≤8 := by omega
 obtain ⟨bd,bp,bm,between,middle,dir,t,source,ending,after,ad,ap,am,j,shape,first,checked,effect,last,
   hero,locks,owner,paid,unchanged,not265,onlyOne⟩ :=
   NorthJCashTen12.split logged completed ten cut.kind cut.shape cut.first cut.checked cut.effect cut.last cut.phase cut.locks
 have atReached := reached.append first.trace
 have atActual := atReached.boulders_nodup (by decide +kernel)
 have old := first.end_subset actual group gUnique gSubset
 have nextActual := step_boulders_nodup _ _ _ _ atActual checked
 have nextUnique := GhostSubset.update_unique _ _ _ effect nextActual _ old.1 old.2
 have nextSubset := GhostSubset.update_subset _ _ _ effect _ old.1 old.2
 have cashBudget : energy p group (between++.push source ending::after)≤8 := by rw [←shape];exact budget
 have make : ∀k : Fin 3,cut.kind=firstKind k→source=secondSource k→dir=.south→Nonempty (SecondJ cut) := by
   intro k kindEq sourceEq south
   have southChecked : step soko1_2.board middle .south=some t := by simpa only [south] using checked
   have endingEq := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
     (by rw [sourceEq];exact targets k) (clear k) southChecked effect
   have shapeB : cut.after=between++B k::after := by
     simpa only [B,sourceEq,endingEq] using shape
   have effectB : Matches middle t (B k) := by simpa only [B,sourceEq,endingEq] using effect
   have fixed : endGroup (C1 k) between=C1 k := by
     have eq : C1 k=AfterJ12.ordinary cut.kind := by rw [kindEq];exact (first_data k).2.symm
     rw [eq]
     exact unchanged _ (fun _ h=>List.mem_append_left _ h)
   exact ⟨{
     path := k,
     firstKindEq := kindEq,
     middle := middle,
     actor := t,
     betweenDirs := bd,
     betweenPushes := bp,
     betweenMoves := bm,
     between := between,
     afterDirs := ad,
     afterPushes := ap,
     afterMoves := am,
     after := after,
     phase := j,
     shape := shapeB,
     gap := first,
     checked := southChecked,
     effect := effectB,
     last := last,
     locks := locks,
     fixedBefore := fixed }⟩
 rcases paid with ordinaryPaid|park|ring
 · obtain ⟨member,direction⟩ := ordinaryPaid
   rcases direction with ⟨choices,south⟩|⟨rfl,west⟩
   · rcases choices with rfl|rfl|rfl|rfl|rfl
     · have eq : cut.kind=1 := (show ∀k,(210:Cell)∈AfterJ12.ordinary k→k=1 from by decide +kernel) cut.kind member
       exact Or.inl (make 2 eq rfl south)
     · have eq : cut.kind=0 := (show ∀k,(236:Cell)∈AfterJ12.ordinary k→k=0 from by decide +kernel) cut.kind member
       exact Or.inl (make 0 eq rfl south)
     · have eq : cut.kind=0 := (show ∀k,(238:Cell)∈AfterJ12.ordinary k→k=0 from by decide +kernel) cut.kind member
       exact Or.inl (make 1 eq rfl south)
     · have kindEq : cut.kind=1 := (show ∀k,(264:Cell)∈AfterJ12.ordinary k→k=1 from by decide +kernel) cut.kind member
       have southChecked : step soko1_2.board middle .south=some t := by simpa only[south] using checked
       have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
        (show pushTargets soko1_2.board 264 .south=[290] by decide +kernel) (by decide +kernel) southChecked effect
       exact Or.inr ⟨{
        kindEq:=kindEq,middle:=middle,actor:=t,betweenDirs:=bd,betweenPushes:=bp,betweenMoves:=bm,between:=between,
        afterDirs:=ad,afterPushes:=ap,afterMoves:=am,after:=after,phase:=j,
        shape:=by simpa only[endingEq] using shape,
        gap:=first,checked:=southChecked,effect:=by simpa only[endingEq] using effect,last:=last,
        locks:=locks,fixedBefore:=unchanged }⟩
     · exact False.elim (not265 rfl)
   · have westChecked : step soko1_2.board middle .west=some t := by simpa only [west] using checked
     have kinds : cut.kind=0∨cut.kind=1 := (show ∀k : Fin 2,k=0∨k=1 from by decide +kernel) cut.kind
     rcases kinds with kindEq|kindEq
     · have blocked : BlockedPush soko1_2.board (AfterJ12.locks cut.kind j) 237 .west := by
         rw [kindEq]
         exact (show ∀j,BlockedPush soko1_2.board (AfterJ12.locks 0 j) 237 .west from by decide +kernel) j
       exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locks old.2) westChecked effect blocked)
     · have endingEq := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 237 .west=[236] by decide +kernel) (by decide +kernel) westChecked effect
       subst ending
       have activation : [210,236]⊆236::(AfterJ12.locks cut.kind j).erase 237 := by
         rw [kindEq]
         exact (show ∀j,([210,236]:List Cell)⊆236::(AfterJ12.locks 1 j).erase 237 from by decide +kernel) j
       have kept := CageFour12.shifted_inside (AfterJ12.unique cut.kind j) locks owner activation
       have future := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
         (update (endGroup group between) (.push 237 (.stay 236))) nextUnique nextSubset
         [210,236] RingAfter12.locked_pair (by decide +kernel) kept
       change 15≤energy p (update (endGroup group between) (.push 237 (.stay 236))) after at future
       have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
       change 0≤ownSlack p group between at nn
       rw [energy_at_split] at cashBudget
       have price : slack p (.push 237 (.stay 236))=2 := by decide +kernel
       have own237 : (237:Cell)∈endGroup group between := owner
       simp only [projectedOutcome,if_pos own237,price] at cashBudget
       omega
 · obtain ⟨rfl,west⟩:=park
   have westChecked : step soko1_2.board middle .west=some t := by simpa only[west] using checked
   have endingEq:=push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
    (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel) (by decide +kernel) westChecked effect
   have parkShape : cut.after=between++.push 318 (.stay 317)::after := by simpa only[endingEq] using shape
   have parkEffect : Matches middle t (.push 318 (.stay 317)) := by simpa only[endingEq] using effect
   have bound:=NorthFirstJPark23112.first_j_then_park logged completed cut parkShape first westChecked parkEffect last j hero locks unchanged
   omega
 · obtain ⟨rfl,west⟩ := ring
   have kindEq := onlyOne rfl
   have westChecked : step soko1_2.board middle .west=some t := by simpa only [west] using checked
   have endingEq := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
     NorthEvents12.ring_activation (by decide +kernel) westChecked effect
   have effect291 : Matches middle t (.push 291 (.stay 290)) := by simpa only [endingEq] using effect
   have firstEffect : Matches cut.middle cut.actor (.push 238 (.stay 264)) := by simpa only [kindEq,first_one] using cut.effect
   have firstShape : outcomes=cut.before++.push 238 (.stay 264)::cut.after := by simpa only [kindEq,first_one] using cut.shape
   let sidecar : AfterJSharpCash12.SidecarCut cut.actor.state
       (update (endGroup NorthBound12.G cut.before) (.push 238 (.stay 264))) final cut.after := {
     middle := middle,
     actor := t,
     beforeDirs := bd,
     beforePushes := bp,
     beforeMoves := bm,
     before := between,
     afterDirs := ad,
     afterPushes := ap,
     afterMoves := am,
     after := after,
     phase := j,
     shape := by simpa only [endingEq] using shape,
     first := first,
     checked := westChecked,
     effect := effect291,
     last := last,
     hero := by simpa only [kindEq] using hero,
     locks := by simpa only [kindEq,first_one] using locks,
     owner := by simpa only [kindEq,first_one] using owner,
     fixedBefore := by simpa only [kindEq] using unchanged }
   have sidecarAt : AfterJSharpCash12.SidecarCut cut.actor.state group final cut.after := by
     simpa only [group,kindEq,first_one] using sidecar
   exact False.elim (SidecarCutEleven12.impossible sidecarAt reached gUnique gSubset completed (by change energy p group cut.after≤10;omega))

#print axioms after_first

/-- At the next whole budget, actual two-J continuations are too expensive;
the critical238South264South290 packet is retained rather than excluded. -/
theorem critical_required {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤230) (gBudget : energy p NorthBound12.G outcomes≤10)
 (cut : NorthFirstJ22812.FirstJ final outcomes) : Nonempty (Critical264 cut) := by
 rcases after_first logged completed cheap gBudget cut with second|critical
 ·obtain ⟨second⟩:=second
  have eleven:=TwoJPriceEleven12.g_eleven logged completed cut second
  change 11≤energy p NorthBound12.G outcomes at eleven
  omega
 ·exact critical
#print axioms critical_required
end Owner1007.NorthAfterFirstTen12
