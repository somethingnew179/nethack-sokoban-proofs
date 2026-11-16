import Owner1007.AfterJCashEight12
import Owner1007.OwnedEventsQuiet12
namespace Owner1007.AfterJCashQuietEight12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.AfterJ12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem split {state final dirs pushes moves outcomes history past pastMoves}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (kind : Fin 2)
 (group : List Cell) (uniqueGroup : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 5) (hero : state.player∈region kind i) (inside : locks kind i⊆group)
 (cheap : energy p group outcomes≤8) :
 ∃ bd bp bm before middle dir t source ending after ad ap am,∃ j : Fin 5,
 outcomes=before++.push source ending::after ∧
 Logged soko1_2.board state bd middle bp bm before ∧
 step soko1_2.board middle dir=some t ∧Matches middle t (.push source ending) ∧
 Logged soko1_2.board t.state ad final ap am after ∧
 middle.player∈region kind j ∧locks kind j⊆endGroup group before ∧
 source∈endGroup group before ∧AfterJ12.paid kind source dir ∧
 (∀small : List Cell,small⊆fixed kind→endGroup small before=small) ∧ownPushes (fixed kind) before=0 ∧
 source≠265 ∧(source=291→kind=1) := by
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
 obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroOne,locksOne,pays,unchanged,quiet⟩ :=
   found.split_quiet (fixed kind) (fixed_inside kind) (fixed_guard kind) reached uniqueGroup subset
 cases outcome with
 | walk target => exact False.elim pays
 | push source ending =>
   obtain ⟨owner,paid⟩ := pays
   have budget : energy p group (before++.push source ending::after)≤8 := by rw [←shape];exact cheap
   have limits := AfterJCashEight12.head_restrictions first checked effect last reached group uniqueGroup subset kind j
     locksOne heroOne owner paid completed budget
   exact ⟨bd,bp,bm,before,middle,dir,t,source,ending,after,ad,ap,am,j,shape,first,
     checked,effect,last,heroOne,locksOne,owner,paid,unchanged,quiet,limits⟩

#print axioms split
end Owner1007.AfterJCashQuietEight12
