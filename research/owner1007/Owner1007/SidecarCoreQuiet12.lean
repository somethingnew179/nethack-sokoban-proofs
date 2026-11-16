import Owner1007.SidecarCore12
import Owner1007.OwnedEventsQuietMore12
import Owner1007.LoggedAppend11
import Owner1007.HeroEnergyTrace11
import Owner1007.TokenBounds32
namespace Owner1007.SidecarCoreQuiet12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.SidecarCore12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def Core (i : Fin 3) : List Cell := [210,237,263,265,if i.val=0 then 238 else if i.val=1 then 264 else 290]
theorem perm : ∀ i,(Core i++[213]).Perm (locks i) := by decide +kernel
theorem core_unique : ∀ i,(Core i).Nodup := by decide +kernel
theorem hero187 : ∀ i,(187:Cell)∈region i := by decide +kernel
theorem quiet_no_event
 {state middle final beforeDirs afterDirs beforePushes beforeMoves afterPushes afterMoves before after}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (last : Logged soko1_2.board middle afterDirs final afterPushes afterMoves after)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (i : Fin 3) (hero : state.player∈region i) (inside : locks i⊆state.boulders)
 (quiet : ownPushes (Core i) before=0)
 (zero187 : energy p [213] (before++after)=0)
 (event : EventLog locks region paid (locks i) state beforeDirs middle beforePushes beforeMoves before) : False := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have lUnique := unique i
 obtain ⟨bd,bp,bm,lead,atHead,dir,t,outcome,tail,ad,ap,am,j,shape,loggedLead,checked,effect,loggedTail,heroHead,locksHead,pays,fixed⟩ :=
   event.split_fixed [213] markers_inside markers_guard reached lUnique inside
 have quietLead : ownPushes (Core i) lead=0 := by
   rw [shape,Hero315Frame11.ownPushes_append] at quiet
   omega
 have coreTag := no_push_unchanged (Core i) lead quietLead
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
   · have split := loggedLead.end_split actualUnique (Core i) [213]
       ((perm i).nodup_iff.mpr lUnique) (List.Subset.trans (perm i).subset inside)
     have transport := endGroup_perm (perm i) lead
     have both := (split.trans transport).mem_iff.mpr owner
     have markerTag := fixed [213] (fun _ h=>h)
     rw [markerTag] at both
     have ownCore : source∈endGroup (Core i) lead := by
       rcases List.mem_append.mp both with found|marker
       · exact found
       · exact False.elim (same (List.mem_singleton.mp marker))
     rw [shape,Hero315Frame11.ownPushes_append] at quiet
     simp only [ownPushes,ownPush,if_pos ownCore] at quiet
     omega


theorem quiet_prefix_good
 {state middle final beforeDirs afterDirs beforePushes beforeMoves afterPushes afterMoves before after}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (last : Logged soko1_2.board middle afterDirs final afterPushes afterMoves after)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (i : Fin 3) (hero : state.player∈region i) (inside : locks i⊆state.boulders)
 (quiet : ownPushes (Core i) before=0)
 (zero187 : energy p [213] (before++after)=0) :
 middle.player∈region i ∧locks i⊆middle.boulders ∧endGroup [213] before=[213] := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 rcases event_or_good_quiet closed unique [213] markers_inside markers_guard
   first reached (locks i) (unique i) inside hero (fun _ h=>h) with event|terminal
 · exact False.elim (quiet_no_event first last reached i hero inside quiet zero187 event)
 · obtain ⟨j,heroEnd,locksEnd,markersQuiet⟩ := terminal
   have coreTag := no_push_unchanged (Core i) before quiet
   have markerTag := no_push_unchanged [213] before markersQuiet
   have split := first.end_split actualUnique (Core i) [213]
     ((perm i).nodup_iff.mpr (unique i)) (List.Subset.trans (perm i).subset inside)
   have transport := endGroup_perm (perm i) before
   have all : (Core i++[213]).Perm (endGroup (locks i) before) := by
     simpa only [coreTag,markerTag] using split.trans transport
   have reverse : endGroup (locks i) before⊆locks i := (all.symm.trans (perm i)).subset
   have initialLocks : locks j⊆locks i := List.Subset.trans locksEnd reverse
   have jSame : j=i := by
     have check : ∀ i j,locks j⊆locks i→j=i := by decide +kernel
     exact check i j initialLocks
   subst j
   have endInside := first.end_subset actualUnique (locks i) (unique i) inside
   exact ⟨heroEnd,List.Subset.trans locksEnd endInside.2,markerTag⟩
#print axioms quiet_no_event
#print axioms quiet_prefix_good

end Owner1007.SidecarCoreQuiet12
