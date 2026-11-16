import Owner1007.Sidecar238To29012
import Owner1007.TokenBounds32
import Owner1007.HeroEnergyTrace11
namespace Owner1007.Sidecar238To29012
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def Core (i : Fin 3) : List Cell := [210,237,263,265,if i.val=0 then 238 else if i.val=1 then 264 else 290]
theorem core_perm : ∀ i,(Core i++[211,213]).Perm (locks i) := by decide +kernel
theorem sizes : ∀ i,(locks i).length=7 := by decide +kernel
theorem separate_source {source dir} (h : paid source dir) (not213 : source≠213) :
 source≠211∧source≠238∧source≠264 := by
 have check : ∀ c∈([210,237,263,265,290,213]:List Cell),c≠213→c≠211∧c≠238∧c≠264 := by decide +kernel
 exact check source (paid_source h) not213

/-- After original187 reaches213, completing the board needs an owned
Core head distinct from both prescribed238South264 and264South290.
The ticket uses the actual original trace and counts neither prescribed head. -/
theorem separate_core_head
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (i : Fin 3)
 (hero : state.player∈region i) (inside : locks i⊆state.boulders)
 (zero187 : energy p [213] outcomes=0) :
 ∃ bd bp bm before middle dir t source ending after ad ap am,
 outcomes=before++.push source ending::after ∧
 Logged soko1_2.board state bd middle bp bm before ∧
 step soko1_2.board middle dir=some t ∧Matches middle t (.push source ending) ∧
 Logged soko1_2.board t.state ad final ap am after ∧
 source∈endGroup (Core i) before ∧source≠238∧source≠264∧
 2≤slack p (.push source ending) := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have found : EventLog locks region paid (locks i) state dirs final pushes moves outcomes := by
   rcases event_or_good closed unique logged reached (locks i) (unique i) inside hero (fun _ h=>h) with event|terminal
   · exact event
   · obtain ⟨j,_,kept⟩ := terminal
     have endInside := logged.end_subset actualUnique (locks i) (unique i) inside
     have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept endInside.2)
     rw [sizes j] at count
     have conserved := (reached.append logged.trace).conservation
     have empty : final.holes=[] := completed
     change 20+final.holes.length=final.boulders.length+18 at conserved
     rw [empty] at conserved
     simp only [List.length_nil] at conserved
     omega
 obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroHead,locksHead,pays,fixed⟩ :=
   found.split_fixed [211,213] markers_inside markers_guard reached (unique i) inside
 have middleReached := reached.append first.trace
 cases outcome with
 | walk target => exact False.elim pays
 | push source ending =>
   obtain ⟨owner,paidHead⟩ := pays
   have price := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset
     (priced source (paid_source paidHead) dir (Geometry.all_directions dir) paidHead) checked effect
   have not213 : source≠213 := by
     intro same
     subst source
     have prior := fixed [213] (by decide +kernel)
     have bound := event_energy_le Generated.soko1_2_potential_valid [213] first last (.push 213 ending)
     rw [prior] at bound
     simp only [projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true] at bound
     rw [←shape] at bound
     change slack p (.push 213 ending)≤energy p [213] outcomes at bound
     omega
   obtain ⟨not211,not238,not264⟩ := separate_source paidHead not213
   have split := first.end_split actualUnique (Core i) [211,213]
     ((core_perm i).nodup_iff.mpr (unique i)) (List.Subset.trans (core_perm i).subset inside)
   have transport := endGroup_perm (core_perm i) before
   have both := (split.trans transport).mem_iff.mpr owner
   have markerTag := fixed [211,213] (fun _ h=>h)
   rw [markerTag] at both
   have ownCore : source∈endGroup (Core i) before := by
     rcases List.mem_append.mp both with found|bad
     · exact found
     · simp only [List.mem_cons,List.not_mem_nil,or_false] at bad
       rcases bad with wrong|wrong
       · exact False.elim (not211 wrong)
       · exact False.elim (not213 wrong)
   exact ⟨bd,bp,bm,before,middle,dir,t,source,ending,after,ad,ap,am,shape,first,checked,effect,last,
     ownCore,not238,not264,price⟩
#print axioms separate_core_head
end Owner1007.Sidecar238To29012
