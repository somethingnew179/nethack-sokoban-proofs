import Owner1007.After291ZeroSeven12
import Owner1007.AfterJParkDeep12
namespace Owner1007.AfterJTightCash12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.AfterJ12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

/-- Prices seven cannot be weakened to six in an equality-case audit. -/
theorem head_restrictions
 {state middle final : State} {t : Transition} {dir : Dir} {source : Cell} {ending : Ending}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle dir=some t)
 (effect : Matches middle t (.push source ending))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (kind : Fin 2) (i : Fin 5) (inside : locks kind i⊆endGroup group before)
 (hero : middle.player∈region kind i) (owner : source∈endGroup group before)
 (paid : AfterJ12.paid kind source dir) (completed : Goal final)
 (cheap : energy p group (before++.push source ending::after)≤6) :
 source≠318 ∧source≠265 ∧(source=291→kind=1) := by
 have middleReached := reached.append first.trace
 have not318 : source≠318 := by
   intro eq
   subst source
   have direction : dir=.west :=
     (show ∀kind,∀dir∈allDirs,AfterJ12.paid kind 318 dir→dir=.west from by decide +kernel) kind dir (Geometry.all_directions dir) paid
   subst dir
   have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
     (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel) (by decide +kernel) checked effect
   subst ending
   have seven := AfterJDeepLate12.after318_seven first checked effect last reached group unique subset
     kind i inside owner hero completed
   change 7≤energy p group (before++.push 318 (.stay 317)::after) at seven
   omega
 have not265 : source≠265 := by
   intro eq
   subst source
   have direction : dir=.south :=
     (show ∀kind,∀dir∈allDirs,AfterJ12.paid kind 265 dir→dir=.south from by decide +kernel) kind dir (Geometry.all_directions dir) paid
   subst dir
   have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
     (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel) (by decide +kernel) checked effect
   subst ending
   have seven := AfterJDeepLeaves12.after265_seven first checked effect last reached group unique subset
     kind i inside completed
   change 7≤energy p group (before++.push 265 (.stay 291)::after) at seven
   omega
 refine ⟨not318,not265,?_⟩
 intro eq
 subst source
 by_cases one : kind=1
 · exact one
 · have zero : kind=0 := Fin.ext (by have bound:=kind.isLt;have neq:=one;omega)
   subst kind
   have direction : dir=.west :=
     (show ∀dir∈allDirs,AfterJ12.paid 0 291 dir→dir=.west from by decide +kernel) dir (Geometry.all_directions dir) paid
   subst dir
   have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
     NorthEvents12.ring_activation (by decide +kernel) checked effect
   subst ending
   have seven := After291ZeroSeven12.after291_seven first checked effect last reached group unique subset
     i inside owner hero completed
   change 7≤energy p group (before++.push 291 (.stay 290)::after) at seven
   omega

/-- Actual first-cash extraction, with the three formerly weakened leaves
removed. The only finite phases here are the five existing corral words. -/
theorem split {state final dirs pushes moves outcomes history past pastMoves}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (kind : Fin 2)
 (group : List Cell) (uniqueGroup : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 5) (hero : state.player∈region kind i) (inside : locks kind i⊆group)
 (cheap : energy p group outcomes≤6) :
 ∃ bd bp bm before middle dir t source ending after ad ap am,∃ j : Fin 5,
 outcomes=before++.push source ending::after ∧
 Logged soko1_2.board state bd middle bp bm before ∧
 step soko1_2.board middle dir=some t ∧Matches middle t (.push source ending) ∧
 Logged soko1_2.board t.state ad final ap am after ∧
 middle.player∈region kind j ∧locks kind j⊆endGroup group before ∧
 source∈endGroup group before ∧AfterJ12.paid kind source dir ∧
 (∀small : List Cell,small⊆fixed kind→endGroup small before=small) ∧
 source≠318 ∧source≠265 ∧(source=291→kind=1) := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ (AfterJBound12.matrices kind)
 have actual := reached.boulders_nodup (by decide +kernel)
 have found : EventLog (locks kind) (region kind) (AfterJ12.paid kind) group state dirs final pushes moves outcomes := by
   rcases event_or_good closed (unique kind) logged reached group uniqueGroup subset hero inside with event|terminal
   · exact event
   · obtain ⟨j,_,selected⟩ := terminal
     have endInside := logged.end_subset actual group uniqueGroup subset
     have count := List.Nodup.length_le_of_subset (unique kind j) (List.Subset.trans selected endInside.2)
     rw [size kind j] at count
     have conserved := (reached.append logged.trace).conservation
     have empty : final.holes=[] := completed
     change 20+final.holes.length=final.boulders.length+18 at conserved
     rw [empty] at conserved
     simp only [List.length_nil] at conserved
     omega
 obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroOne,locksOne,pays,unchanged⟩ :=
   found.split_fixed (fixed kind) (fixed_inside kind) (fixed_guard kind) reached uniqueGroup subset
 cases outcome with
 | walk target => exact False.elim pays
 | push source ending =>
   obtain ⟨owner,paid⟩ := pays
   have budget : energy p group (before++.push source ending::after)≤6 := by rw [←shape];exact cheap
   have limits := head_restrictions first checked effect last reached group uniqueGroup subset kind j
     locksOne heroOne owner paid completed budget
   exact ⟨bd,bp,bm,before,middle,dir,t,source,ending,after,ad,ap,am,j,shape,first,
     checked,effect,last,heroOne,locksOne,owner,paid,unchanged,limits⟩
#print axioms head_restrictions
#print axioms split
end Owner1007.AfterJTightCash12
