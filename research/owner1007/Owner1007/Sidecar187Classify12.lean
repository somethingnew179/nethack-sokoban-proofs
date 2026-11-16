import Owner1007.SidecarCoreQuiet12
import Owner1007.Upper187ForcedSouth12
namespace Owner1007.Sidecar187Classify12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.SidecarCoreQuiet12
open Owner1007.SidecarCore12 (locks region)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- With the Core stationary and original187's full energy zero, a quiet
prefix leaves187 either at187 or at213 on the sealed side of the Core. -/
theorem classify
 {state middle final beforeDirs afterDirs beforePushes beforeMoves afterPushes afterMoves before after}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (last : Logged soko1_2.board middle afterDirs final afterPushes afterMoves after)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (i : Fin 3) (coreInside : Core i⊆state.boulders)
 (quiet : ownPushes (Core i) before=0)
 (zero187 : energy p [187] (before++after)=0) :
 endGroup [187] before=[187] ∨
 (endGroup [187] before=[213] ∧middle.player∈region i ∧locks i⊆middle.boulders) := by
 by_cases stationary : ownPushes [187] before=0
 · exact Or.inl (no_push_unchanged [187] before stationary)
 · have moved : 0<ownPushes [187] before := Nat.pos_of_ne_zero stationary
   obtain ⟨bd,bp,bm,lead,atHead,dir,t,source,ending,tail,ad,ap,am,shape,loggedLead,checked,effect,loggedTail,still,member⟩ :=
     FirstOwnedPush.first_push first [187] moved
   have sourceEq : source=187 := List.mem_singleton.mp member
   subst source
   have tag187 := no_push_unchanged [187] lead still
   have leadQuiet : ownPushes (Core i) lead=0 := by
     rw [shape,Hero315Frame11.ownPushes_append] at quiet
     omega
   have tagCore := no_push_unchanged (Core i) lead leadQuiet
   have actualUnique := reached.boulders_nodup (by decide +kernel)
   have atReached := reached.append loggedLead.trace
   have atUnique := atReached.boulders_nodup (by decide +kernel)
   have coreSelected := loggedLead.end_subset actualUnique (Core i) (core_unique i) coreInside
   have coreAt : Core i⊆atHead.boulders := by simpa only [tagCore] using coreSelected.2
   have standing := step_player_clear soko1_2.board atHead dir t checked
   have present : (187:Cell)∈atHead.boulders := by cases ending <;> exact effect.1
   obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
   have wholeTail := loggedTail.append last
   have wholeShape : before++after=lead++.push 187 ending::(tail++after) := by
     rw [shape]
     simp only [List.append_assoc,List.cons_append]
   rcases Upper187ForcedSouth12.direction_cases atHead.player standing.1 dir
       (Geometry.all_directions dir) adjacent with blocked|north|south
   · exact False.elim (CageFour12.blocked_impossible (by simpa using present) checked effect blocked)
   · subst dir
     have price := push_effect_price p soko1_2.initial.holes 2 atReached.holes_sublist.subset
       (show ∀ dest∈pushTargets soko1_2.board 187 .north,
         dest∉soko1_2.initial.holes ∧(2:Int)≤1+p.boulder dest-p.boulder 187 from by decide +kernel) checked effect
     have lower := event_energy_le Generated.soko1_2_potential_valid [187] loggedLead wholeTail (.push 187 ending)
     rw [tag187] at lower
     simp only [projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true] at lower
     rw [←wholeShape] at lower
     change slack p (.push 187 ending)≤energy p [187] (before++after) at lower
     omega
   · subst dir
     have sameEnding := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
       (show pushTargets soko1_2.board 187 .south=[213] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     have notCore : (187:Cell)∉Core i := by
       have check : ∀ i,(187:Cell)∉Core i := by decide +kernel
       exact check i
     have coreUpdate : update (Core i) (.push 187 (.stay 213))=Core i := by
       simp only [update,move,if_neg notCore]
     have tailQuiet : ownPushes (Core i) tail=0 := by
       rw [shape,Hero315Frame11.ownPushes_append,tagCore] at quiet
       simp only [ownPushes,ownPush,if_neg notCore,coreUpdate,Nat.zero_add] at quiet
       omega
     have nextActual := step_boulders_nodup _ _ _ _ atUnique checked
     have coreNext := GhostSubset.update_subset atHead t (.push 187 (.stay 213)) effect
       (Core i) (core_unique i) coreAt
     rw [coreUpdate] at coreNext
     have next213 : (213:Cell)∈t.state.boulders := by
       rw [effect.2]
       exact List.mem_cons_self
     have physical : locks i⊆t.state.boulders := by
       have check : ∀ i,locks i⊆Core i++[213] := by decide +kernel
       intro c found
       rcases List.mem_append.mp (check i found) with core|single
       · exact coreNext core
       · have same : c=213 := List.mem_singleton.mp single
         simpa only [same] using next213
     have nextReached := atReached.append (Trace.cons checked (Trace.nil t.state))
     have hero : t.state.player∈region i := by
       rw [matches_hero atHead t (.push 187 (.stay 213)) effect]
       exact hero187 i
     have split187 : energy p [187] (before++after)=ownSlack p [187] lead+energy p [213] (tail++after) := by
       rw [wholeShape,energy_at_split,tag187]
       have one : slack p (.push 187 (.stay 213))=0 := by decide +kernel
       simp only [projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true,one,Int.add_zero]
       rfl
     have nn := loggedLead.ownSlack_nonnegative Generated.soko1_2_potential_valid [187]
     have laterNN := wholeTail.energy_nonnegative Generated.soko1_2_potential_valid [213]
     change 0≤ownSlack p [187] lead at nn
     change 0≤energy p [213] (tail++after) at laterNN
     have zero213 : energy p [213] (tail++after)=0 := by omega
     obtain ⟨lastHero,lastLocks,lastTag⟩ := quiet_prefix_good loggedTail last nextReached
       i hero physical tailQuiet zero213
     have finalTag : endGroup [187] before=[213] := by
       rw [shape,endGroup_append,tag187]
       change endGroup [213] tail=[213]
       exact lastTag
     exact Or.inr ⟨finalTag,lastHero,lastLocks⟩
#print axioms classify
end Owner1007.Sidecar187Classify12
