import Owner1007.Sidecar264Gate12
import Owner1007.HeroEnergyTrace11
import Owner1007.TokenBounds32
import Owner1007.LoggedAppend11
namespace Owner1007.Sidecar264Quiet12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.Sidecar264Gate12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def Core : List Cell := [210,237,264,263,265]
theorem perm : (Core++[211,213]).Perm (locks 0) := by decide +kernel
theorem core_size : Core.Nodup := by decide +kernel
theorem core_actual {state : State} (inside : locks 0⊆state.boulders) : Core⊆state.boulders :=
 List.Subset.trans (by decide +kernel : Core⊆locks 0) inside
/-- Prior to the next fixed-Core push, original187 at213 cannot obtain
the support214 needed for its zero-price west push. -/
theorem quiet_support_impossible
 {state middle final beforeDirs afterDirs beforePushes beforeMoves afterPushes afterMoves before after}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (last : Logged soko1_2.board middle afterDirs final afterPushes afterMoves after)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (hero : state.player∈region 0) (inside : locks 0⊆state.boulders)
 (quiet : ownPushes Core before=0)
 (zero187 : energy p [213] (before++after)=0)
 (support : middle.player=214) : False := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have lUnique := unique 0
 obtain event := support_has_event first reached (locks 0) lUnique inside hero (fun _ h=>h) support
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
#print axioms quiet_support_impossible
end Owner1007.Sidecar264Quiet12
