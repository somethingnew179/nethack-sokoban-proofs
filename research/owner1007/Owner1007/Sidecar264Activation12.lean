import Owner1007.Sidecar264Quiet12
import Owner1007.OwnedEventsQuietMore12
namespace Owner1007.Sidecar264Quiet12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.Sidecar264Gate12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem quiet_no_event
 {state middle final beforeDirs afterDirs beforePushes beforeMoves afterPushes afterMoves before after}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (last : Logged soko1_2.board middle afterDirs final afterPushes afterMoves after)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (hero : state.player∈region 0) (inside : locks 0⊆state.boulders)
 (quiet : ownPushes Core before=0)
 (zero187 : energy p [213] (before++after)=0)
 (event : EventLog locks region paid (locks 0) state beforeDirs middle beforePushes beforeMoves before) : False := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have lUnique := unique 0
 obtain ⟨bd,bp,bm,lead,atHead,dir,t,outcome,tail,ad,ap,am,i,shape,loggedLead,checked,effect,loggedTail,heroHead,locksHead,pays,fixed⟩ :=
   event.split_fixed [211,213] markers_inside markers_guard reached lUnique inside
 have quietLead : ownPushes Core lead=0 := by
   rw [shape,Hero315Frame11.ownPushes_append] at quiet
   omega
 have coreTag := no_push_unchanged Core lead quietLead
 have middleReached := reached.append loggedLead.trace
 cases outcome with
 | walk target => exact pays
 | push source ending =>
   obtain ⟨owner,paidHead⟩ := pays
   have price := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset
     (priced source (paid_source paidHead) dir (Geometry.all_directions dir) paidHead) checked effect
   by_cases same : source=213
   · subst source
     have originalTag := fixed [213] (by decide +kernel)
     have wholeTail := loggedTail.append last
     have lower := event_energy_le Generated.soko1_2_potential_valid [213] loggedLead wholeTail (.push 213 ending)
     rw [originalTag] at lower
     simp only [projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true] at lower
     have wholeShape : before++after=lead++.push 213 ending::(tail++after) := by
       rw [shape]
       simp only [List.append_assoc,List.cons_append]
     rw [←wholeShape] at lower
     change slack p (.push 213 ending)≤energy p [213] (before++after) at lower
     omega
   · have split := loggedLead.end_split actualUnique Core [211,213]
       (perm.nodup_iff.mpr lUnique) (List.Subset.trans perm.subset inside)
     have transport := endGroup_perm perm lead
     have both := (split.trans transport).mem_iff.mpr owner
     have markerTag := fixed [211,213] (fun _ h=>h)
     rw [markerTag] at both
     have ownCore : source∈endGroup Core lead := by
       rcases List.mem_append.mp both with found|marker
       · exact found
       · have others : source≠211 := by
           have check : ∀ c∈([210,237,263,265,290,213]:List Cell),c≠211 := by decide +kernel
           exact check source (paid_source paidHead)
         simp only [List.mem_cons,List.not_mem_nil,or_false] at marker
         rcases marker with wrong|wrong
         · exact False.elim (others wrong)
         · exact False.elim (same wrong)
     rw [shape,Hero315Frame11.ownPushes_append] at quiet
     simp only [ownPushes,ownPush,if_pos ownCore] at quiet
     omega

theorem quiet_subgroup (small large : List Cell) (outcomes : List Outcome)
 (subset : small⊆large) (zero : ownPushes large outcomes=0) : ownPushes small outcomes=0 := by
 induction outcomes generalizing small large with
 | nil => rfl
 | cons outcome rest ih =>
   have headZero : ownPush large outcome=0 := by simp only [ownPushes] at zero;omega
   have sameLarge := ownPush_zero_update large outcome headZero
   have headSmall : ownPush small outcome=0 := by
     cases outcome with
     | walk target => rfl
     | push source ending =>
       have absent : source∉large := by
         intro found
         simp only [ownPush,if_pos found] at headZero
         omega
       have notSmall : source∉small := fun h=>absent (subset h)
       simp only [ownPush,if_neg notSmall]
   have sameSmall := ownPush_zero_update small outcome headSmall
   have tailZero : ownPushes large rest=0 := by
     simpa only [ownPushes,headZero,sameLarge,Nat.zero_add] using zero
   have tailSmall := ih small large subset tailZero
   simpa only [ownPushes,headSmall,sameSmall,Nat.zero_add] using tailSmall

/-- A quiet actual prefix after187South remains on the precritical side,
with the original187 still exactly at213. -/
theorem quiet_prefix_good
 {state middle final beforeDirs afterDirs beforePushes beforeMoves afterPushes afterMoves before after}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (last : Logged soko1_2.board middle afterDirs final afterPushes afterMoves after)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (hero : state.player∈region 0) (inside : locks 0⊆state.boulders)
 (quiet : ownPushes Core before=0)
 (zero187 : energy p [213] (before++after)=0) :
 middle.player∈region 0 ∧locks 0⊆middle.boulders ∧endGroup [213] before=[213] := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 rcases event_or_good_quiet closed unique [211,213] markers_inside markers_guard
   first reached (locks 0) (unique 0) inside hero (fun _ h=>h) with event|terminal
 · exact False.elim (quiet_no_event first last reached hero inside quiet zero187 event)
 · obtain ⟨j,heroEnd,locksEnd,markersQuiet⟩ := terminal
   have coreTag := no_push_unchanged Core before quiet
   have markerTag := no_push_unchanged [211,213] before markersQuiet
   have split := first.end_split actualUnique Core [211,213]
     (perm.nodup_iff.mpr (unique 0)) (List.Subset.trans perm.subset inside)
   have transport := endGroup_perm perm before
   have all : (Core++[211,213]).Perm (endGroup (locks 0) before) := by
     simpa only [coreTag,markerTag] using split.trans transport
   have reverse : endGroup (locks 0) before⊆locks 0 := (all.symm.trans perm).subset
   have initialLocks : locks j⊆locks 0 := List.Subset.trans locksEnd reverse
   have jZero : j=0 := by
     have check : ∀ j,locks j⊆locks 0→j=(0:Fin 2) := by decide +kernel
     exact check j initialLocks
   subst j
   have endInside := first.end_subset actualUnique (locks 0) (unique 0) inside
   have originalQuiet := quiet_subgroup [213] [211,213] before (by decide +kernel) markersQuiet
   exact ⟨heroEnd,List.Subset.trans locksEnd endInside.2,no_push_unchanged [213] before originalQuiet⟩
#print axioms quiet_no_event
#print axioms quiet_prefix_good

end Owner1007.Sidecar264Quiet12
