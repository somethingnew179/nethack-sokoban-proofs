import Owner1007.TaggedFlow12
import Owner1007.RingTagFacts12
import Owner1007.PreRingHeads12
import Owner1007.CageLedger12
import Owner1007.VerticalPair12
import Owner1007.RingCageSix12
import Owner1007.TokenCounting
import Owner1007.RingCheap12
import Owner1007.CageFour12
namespace Owner1007.RingPrepared12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem extra_four
 {state middle next final beforeDirs afterDirs beforePushes beforeMoves afterPushes afterMoves before after}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 {source dir ending} (checked : step soko1_2.board middle dir=some next)
 (effect : Matches middle next (.push source ending))
 (last : Logged soko1_2.board next.state afterDirs final afterPushes afterMoves after)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (owner : source∈endGroup group before)
 (hero : middle.player∈RingCut12.region 0)
 (inside : RingCut12.locks 0⊆endGroup group before)
 (avoid : ¬RingCut12.paid source dir) (two : 2≤slack p (.push source ending))
 (completed : Goal final) :
 4≤energy p group (before++ .push source ending::after) := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have oldGroup := first.end_subset actualUnique group unique subset
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle next (.push source ending) effect nextActual
   (endGroup group before) oldGroup.1 oldGroup.2
 have nextSubset := GhostSubset.update_subset middle next (.push source ending) effect
   (endGroup group before) oldGroup.1 oldGroup.2
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil next.state))
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ RingCut12.matrix
 have avoids : ¬PaidOutcome RingCut12.paid dir (endGroup group before) (.push source ending) := by
   intro h
   exact avoid h.2
 obtain ⟨i,nextHero,nextInside⟩ := owned_step_good_except closed RingCut12.unique
   middle middleUnique middleReached.holes_sublist.subset
   (RightEnergy12.trace_disjoint middleReached RightEnergy12.initial_disjoint)
   (endGroup group before) oldGroup.1 oldGroup.2 hero inside dir next checked (.push source ending) effect avoids
 have only : i=0 := Subsingleton.elim i 0
 subst i
 have later := closedExcept_energy closed RingCut12.unique (by decide +kernel) 2 NorthBound12.ring_priced
   last nextReached (update (endGroup group before) (.push source ending))
   nextUnique nextSubset completed nextHero nextInside
 change 2≤energy p (update (endGroup group before) (.push source ending)) after at later
 have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group before at nn
 rw [energy_at_split]
 simp only [projectedOutcome,if_pos owner]
 omega

theorem after_paid_two {state final : State}
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 {dir t source ending}
 (checked : step soko1_2.board state dir=some t)
 (effect : Matches state t (.push source ending))
 {afterDirs afterPushes afterMoves after}
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (inside : RingCut12.locks 0⊆group) (paid : RingCut12.paid source dir)
 (different : source≠263) (completed : Goal final) :
 2≤energy p (update group (.push source ending)) after := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
 have nextUnique := GhostSubset.update_unique state t (.push source ending) effect nextActual group unique subset
 have nextSubset := GhostSubset.update_subset state t (.push source ending) effect group unique subset
 have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
 rcases paid with h|h|h|h
 · obtain ⟨rfl,rfl⟩:=h
   have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     (show pushTargets soko1_2.board 210 .south=[236] by decide +kernel)
     (by decide +kernel) checked effect
   subst ending
   have owner : (210:Cell)∈group := inside (by decide +kernel)
   have newInside : RingAfter12.locks false 0⊆update group (.push 210 (.stay 236)) := by
     apply CageFour12.shifted_inside (RingCut12.unique 0) inside owner
     decide +kernel
   have newHero : t.state.player∈RingAfter12.region false 0 := by
     rw [matches_hero state t (.push 210 (.stay 236)) effect]
     decide +kernel
   exact RingAfter12.owned_energy_two false last nextReached _ nextUnique nextSubset completed newHero newInside
 · obtain ⟨rfl,rfl⟩:=h
   have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     (show pushTargets soko1_2.board 237 .west=[236] by decide +kernel)
     (by decide +kernel) checked effect
   subst ending
   have owner : (237:Cell)∈group := inside (by decide +kernel)
   have newInside : [210,236]⊆update group (.push 237 (.stay 236)) := by
     apply CageFour12.shifted_inside (RingCut12.unique 0) inside owner
     decide +kernel
   have bound := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
     (update group (.push 237 (.stay 236))) nextUnique nextSubset
     [210,236] RingAfter12.locked_pair (by decide +kernel) newInside
   have high : (2:Int)≤debtOf p [210,236] := by decide +kernel
   change debtOf p [210,236]≤energy p (update group (.push 237 (.stay 236))) after at bound
   omega
 · obtain ⟨rfl,rfl⟩:=h
   exact False.elim (different rfl)
 · obtain ⟨rfl,rfl⟩:=h
   have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     (show pushTargets soko1_2.board 290 .west=[289] by decide +kernel)
     (by decide +kernel) checked effect
   subst ending
   have owner : (290:Cell)∈group := inside (by decide +kernel)
   have newInside : RingAfter12.locks true 0⊆update group (.push 290 (.stay 289)) := by
     apply CageFour12.shifted_inside (RingCut12.unique 0) inside owner
     decide +kernel
   have newHero : t.state.player∈RingAfter12.region true 0 := by
     rw [matches_hero state t (.push 290 (.stay 289)) effect]
     decide +kernel
   exact RingAfter12.owned_energy_two true last nextReached _ nextUnique nextSubset completed newHero newInside

open Owner1007.PreCage12 Owner1007.RingTagFacts12
def G (i : Fin 4) : List Cell := [210,237,238,263,290,ringTag i]
def UP (i : Fin 4) : List Cell := U++[ringS i]
def L (i : Fin 4) : List Cell := U++([ringS i]++G i)
theorem framePerm : ∀ i, (L i).Perm (ringLocks i) := by decide +kernel
theorem uniqueL : ∀ i, (L i).Nodup := by decide +kernel
theorem uniqueG : ∀ i, (G i).Nodup := by decide +kernel
theorem uniqueUP : ∀ i, (UP i).Nodup := by decide +kernel
theorem initialG : ∀ i, RingCut12.locks 0⊆G i := by decide +kernel
theorem ringBonus : ∀ i, ∀ hero∈ringRegion i,
 RightEnergy12.cert.bonus hero (NetHack.Sokoban.PatternCorrection.project U)=2 := by decide +kernel

theorem uInL : ∀ i, U⊆L i := by decide +kernel
theorem gInL : ∀ i, G i⊆L i := by decide +kernel
theorem upInL : ∀ i, UP i⊆L i := by decide +kernel
theorem restInL : ∀ i, [ringS i]++G i⊆L i := by decide +kernel
theorem restUnique : ∀ i, ([ringS i]++G i).Nodup := by decide +kernel
theorem g_sources : ∀ i, ∀ source∈PreRingHeads12.sources,
 source∈ringLocks i → source∉U → source≠ringS i → source∈G i := by decide +kernel
theorem g_fixed_inside : ([210,237,263,290] : List Cell)⊆[210,237,238,263,290] := by decide +kernel

theorem frame_six {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (i : Fin 4)
 (hero : state.player∈ringRegion i) (subset : L i⊆state.boulders) :
 6≤energy p (L i) outcomes := by
 by_cases high : 6≤energy p (L i) outcomes
 · exact high
 · have cheapL : energy p (L i) outcomes≤5 := by omega
   exfalso
   have actualUnique := reached.boulders_nodup (by decide +kernel)
   have uSubset : U⊆state.boulders := List.Subset.trans (uInL i) subset
   have gSubset : G i⊆state.boulders := List.Subset.trans (gInL i) subset
   have upSubset : UP i⊆state.boulders := List.Subset.trans (upInL i) subset
   have restSubset : [ringS i]++G i⊆state.boulders := List.Subset.trans (restInL i) subset
   have upper := RightEnergy12.raw_group_energy logged reached U (by decide +kernel) uSubset completed
   rw [ringBonus i state.player hero] at upper
   change 2≤energy p U outcomes at upper
   have ringClosed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ RingCut12.matrix
   have gTwo := closedExcept_energy ringClosed RingCut12.unique (by decide +kernel) 2 NorthBound12.ring_priced
     logged reached (G i) (uniqueG i) gSubset completed (PreRingHeads12.ring_region_inside i hero) (initialG i)
   change 2≤energy p (G i) outcomes at gTwo
   have a := logged.energy_split actualUnique p U ([ringS i]++G i) (uniqueL i) subset
   change energy p (L i) outcomes=energy p U outcomes+energy p ([ringS i]++G i) outcomes at a
   have b := logged.energy_split actualUnique p [ringS i] (G i) (restUnique i) restSubset
   have upSplit := logged.energy_split actualUnique p U [ringS i] (uniqueUP i) upSubset
   change energy p (UP i) outcomes=energy p U outcomes+energy p [ringS i] outcomes at upSplit
   have nnS := logged.energy_nonnegative Generated.soko1_2_potential_valid [ringS i]
   change 0≤energy p [ringS i] outcomes at nnS
   have cheapUP : energy p (UP i) outcomes≤3 := by omega
   have cheapS : energy p [ringS i] outcomes≤1 := by omega
   have cheapG : energy p (G i) outcomes≤3 := by omega
   have initialInside : ringLocks i⊆L i := fun _ h => (framePerm i).mem_iff.mpr h
   rcases TaggedFlow12.event_or_good ring_closed ring_unique ring_tags_inside ring_tag_sound ring_tag_update
     logged reached (L i) [ringS i] [ringTag i] (uniqueL i) subset
     hero initialInside rfl rfl with event | terminal
   · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
       afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locks,pays,sAt,tAt,unchanged⟩ :=
       event.split_fixed ringFixed ring_fixed_inside ring_fixed_guard reached (uniqueL i) subset
     have middleReached := reached.append first.trace
     have middleUnique := middleReached.boulders_nodup (by decide +kernel)
     have physical := first.end_subset actualUnique (L i) (uniqueL i) subset
     have oldG := first.end_subset actualUnique (G i) (uniqueG i) gSubset
     have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
     have nextSelectedUnique := GhostSubset.update_unique middle t outcome effect nextActual
       (endGroup (L i) before) physical.1 physical.2
     have nextSelectedSubset := GhostSubset.update_subset middle t outcome effect
       (endGroup (L i) before) physical.1 physical.2
     have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
     have gFixed := unchanged [210,237,238,263,290] (by intro c h; exact List.mem_append_right _ h)
     have gIdentity := first.end_split actualUnique [210,237,238,263,290] [ringTag i] (uniqueG i) gSubset
     rw [gFixed,tAt] at gIdentity
     change (G j).Perm (endGroup (G i) before) at gIdentity
     have ringInsideG : RingCut12.locks 0⊆endGroup (G i) before := fun _ h =>
       gIdentity.mem_iff.mp (initialG j h)
     have heroRing := PreRingHeads12.ring_region_inside j heroBefore
     have sourceMember (source : Cell) (owner : source∈endGroup (L i) before) : source∈ringLocks j := by
       apply Classical.byContradiction
       intro absent
       have allInside : source::ringLocks j⊆endGroup (L i) before := by
         intro cell found
         rcases List.mem_cons.mp found with rfl|member
         · exact owner
         · exact locks member
       have count := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨absent,ring_unique j⟩) allInside
       have size := ring_size j
       have bound := endGroup_length_le (L i) before
       have total : (L i).length=12 := by
         have all : ∀ i, (L i).length=12 := by decide +kernel
         exact all i
       simp only [List.length_cons] at count
       omega
     cases outcome with
     | walk target => exact False.elim pays
     | push source ending =>
       obtain ⟨owner,paid⟩ := pays
       have inSources := PreRingHeads12.source_cases source dir paid
       obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
       have classified := PreRingHeads12.classification j middle.player heroBefore dir source inSources adjacent paid
       rcases classified with blocked|mainRing|upperHead|square|extra
       · exact CageFour12.blocked_impossible (List.Subset.trans locks physical.2) checked effect blocked
       · have ringMember : source∈RingCut12.locks 0 := by
           rcases mainRing with h|h|h|h <;> simp_all [RingCut12.locks]
         have ownerG := ringInsideG ringMember
         by_cases chosen : source=263
         · subst source
           have west : dir=.west := by rcases mainRing with h|h|h|h <;> simp_all
           subst dir
           have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
             (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel) (by decide +kernel) checked effect
           subst ending
           have six := RingCageSix12.energy_six first checked effect last reached
             (L i) (uniqueL i) subset j locks completed
           change 6≤energy p (L i) (before++(.push 263 (.stay 262))::after) at six
           rw [shape] at cheapL
           omega
         · have later := after_paid_two middleReached checked effect last
             (endGroup (G i) before) oldG.1 oldG.2 ringInsideG mainRing chosen completed
           have price := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset
             (NorthBound12.ring_priced source dir mainRing) checked effect
           have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid (G i)
           change 0≤ownSlack p (G i) before at prefixNN
           rw [shape,energy_at_split] at cheapG
           simp only [projectedOutcome,if_pos ownerG] at cheapG
           omega
       · obtain ⟨rfl,rfl,at212⟩:=upperHead
         have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
           (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel) (by decide +kernel) checked effect
         subst ending
         have upperSame := unchanged U (by intro c h; exact List.mem_append_left _ h)
         have identity := first.end_split actualUnique U [ringS i] (uniqueUP i) upSubset
         rw [upperSame,sAt,at212] at identity
         change (U++[212]).Perm (endGroup (UP i) before) at identity
         have pairInside : ([186,212] : List Cell)⊆endGroup (UP i) before := by
           intro c member
           apply identity.mem_iff.mp
           have all : ([186,212] : List Cell)⊆U++[212] := by decide +kernel
           exact all member
         have ownerUP : (187:Cell)∈endGroup (UP i) before := identity.mem_iff.mp (by decide +kernel)
         have oldUP := first.end_subset actualUnique (UP i) (uniqueUP i) upSubset
         have nextUPUnique := GhostSubset.update_unique middle t (.push 187 (.stay 161)) effect nextActual
           (endGroup (UP i) before) oldUP.1 oldUP.2
         have nextUPSubset := GhostSubset.update_subset middle t (.push 187 (.stay 161)) effect
           (endGroup (UP i) before) oldUP.1 oldUP.2
         have pairAfter := update_mono [186,212] (endGroup (UP i) before) (by decide +kernel) pairInside (.push 187 (.stay 161))
         simp only [update,move,if_neg (show (187:Cell)∉[186,212] by decide)] at pairAfter
         have heroPair : t.state.player∈VerticalPair12.region false 0 := by
           rw [matches_hero middle t (.push 187 (.stay 161)) effect]
           decide +kernel
         have later := VerticalPair12.owned_energy_two false last nextReached
           (update (endGroup (UP i) before) (.push 187 (.stay 161))) nextUPUnique nextUPSubset heroPair pairAfter
         change 2≤energy p (update (endGroup (UP i) before) (.push 187 (.stay 161))) after at later
         have price : (2:Int)≤slack p (.push 187 (.stay 161)) := by decide +kernel
         have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid (UP i)
         change 0≤ownSlack p (UP i) before at prefixNN
         rw [shape,energy_at_split] at cheapUP
         simp only [projectedOutcome,if_pos ownerUP] at cheapUP
         omega
       · rcases square with h|h
         · obtain ⟨rfl,rfl,shifted⟩:=h
           have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
             PreRingHeads12.square_targets.1 (by decide +kernel) checked effect
           subst ending
           have kept := CageFour12.shifted_inside (ring_unique j) locks owner shifted
           have actualSquare := List.Subset.trans kept nextSelectedSubset
           exact square12_excluded nextReached last.trace completed actualSquare
         · obtain ⟨rfl,rfl,shifted⟩:=h
           have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
             PreRingHeads12.square_targets.2 (by decide +kernel) checked effect
           subst ending
           have kept := CageFour12.shifted_inside (ring_unique j) locks owner shifted
           have actualSquare := List.Subset.trans kept nextSelectedSubset
           exact square12_excluded nextReached last.trace completed actualSquare
       · have price := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset extra.2.2 checked effect
         by_cases same : source=ringS j
         · have ownerS : source∈endGroup [ringS i] before := by rw [sAt]; exact List.mem_singleton.mpr same
           have bound := event_energy_le Generated.soko1_2_potential_valid [ringS i] first last (.push source ending)
           simp only [projectedOutcome,if_pos ownerS] at bound
           change slack p (.push source ending)≤energy p [ringS i] (before++(.push source ending)::after) at bound
           rw [shape] at cheapS
           omega
         · have ownerG := gIdentity.mem_iff.mp (g_sources j source inSources (sourceMember source owner) extra.1 same)
           have four := extra_four first reached checked effect last (G i) (uniqueG i) gSubset
             ownerG heroRing ringInsideG extra.2.1 price completed
           change 4≤energy p (G i) (before++(.push source ending)::after) at four
           rw [shape] at cheapG
           omega
   · obtain ⟨j,hero,locks,_,_⟩:=terminal
     have finalInside := logged.end_subset actualUnique (L i) (uniqueL i) subset
     have count := List.Nodup.length_le_of_subset (ring_unique j) (List.Subset.trans locks finalInside.2)
     have size := ring_size j
     have conserved := (reached.append logged.trace).conservation
     have empty : final.holes=[] := completed
     change 20+final.holes.length=final.boulders.length+18 at conserved
     rw [empty] at conserved
     simp only [List.length_nil] at conserved
     omega

theorem ring_energy_six {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 4}
 (hero : state.player∈ringRegion i) (inside : ringLocks i⊆group) :
 6≤energy p group outcomes := by
 have selectedInside : L i⊆group := fun _ h => inside ((framePerm i).mem_iff.mp h)
 have selectedActual := List.Subset.trans selectedInside subset
 have six := frame_six logged reached completed i hero selectedActual
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have mono := logged.energy_mono Generated.soko1_2_potential_valid actualUnique
   (L i) group (uniqueL i) unique selectedActual subset selectedInside
 change energy p (L i) outcomes≤energy p group outcomes at mono
 exact Int.le_trans six mono

#print axioms frame_six
#print axioms ring_energy_six
end Owner1007.RingPrepared12

