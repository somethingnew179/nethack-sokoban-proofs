import Owner1007.Upper187FirstGeometry12
import Owner1007.NorthUpperTwoConsumed12
import Owner1007.CageFour12
import Owner1007.HeroEnergyTrace11
namespace Owner1007.Upper187Start12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.Upper187FirstGeometry12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev U := PreCage12.U
def Others : List Cell := [108,158,159,186]
theorem first_north_four
 {initial : State} {initialDirs : List Dir} {initialPushes initialMoves : Nat}
 (initialReached : Trace soko1_2.board soko1_2.initial initialDirs initial initialPushes initialMoves)
 (uInside : U⊆initial.boulders) (heroInitial : initial.player∈Upper187FirstGeometry12.region 0)
 {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_2.board initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_2.board state .north=some t) (effect : Matches state t (.push 187 (.stay 161)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (stationary : ownPushes [187] before=0) :
 4≤energy p U (before++.push 187 (.stay 161)::after) := by
 have actualUnique := initialReached.boulders_nodup (by decide +kernel)
 have othersInside : Others⊆initial.boulders := List.Subset.trans (by decide +kernel : Others⊆U) uInside
 have singletonInside : ([187]:List Cell)⊆initial.boulders := List.Subset.trans (by decide +kernel : ([187]:List Cell)⊆U) uInside
 by_cases enough : 4≤energy p U (before++.push 187 (.stay 161)::after)
 · exact enough
 · have cheap : energy p U (before++.push 187 (.stay 161)::after)<4 := by omega
   have tag := no_push_unchanged [187] before stationary
   let whole := first.append (Logged.cons head effect last)
   have singleton := event_energy_le Generated.soko1_2_potential_valid [187] first last (.push 187 (.stay 161))
   change slack p (projectedOutcome (endGroup [187] before) (.push 187 (.stay 161)))≤energy p [187] (before++.push 187 (.stay 161)::after) at singleton
   rw [tag] at singleton
   have amount : slack p (projectedOutcome [187] (.push 187 (.stay 161)))=2 := by decide +kernel
   rw [amount] at singleton
   have sum := whole.energy_split (by first | assumption | decide +kernel) p Others [187] (by first | assumption | decide +kernel) (by first | assumption | decide +kernel)
   change energy p U (before++.push 187 (.stay 161)::after)=
     energy p Others (before++.push 187 (.stay 161)::after)+energy p [187] (before++.push 187 (.stay 161)::after) at sum
   have othersCheap : energy p Others (before++.push 187 (.stay 161)::after)<2 := by omega
   have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
   have actualUnique : initial.boulders.Nodup := initialReached.boulders_nodup (by first | assumption | decide +kernel)
   rcases event_or_good closed unique first initialReached U (by first | assumption | decide +kernel) (by first | assumption | decide +kernel)
     (i:=0) (by first | assumption | decide +kernel) (by first | assumption | decide +kernel) with event|terminal
   · obtain ⟨d1,p1,m1,o1,mid,dir,actor,outcome,o2,d2,p2,m2,j,shape,lead,checked,matched,tail,hero,inside,pays⟩ := event.split
     have prefixZero : ownPushes [187] o1=0 := by
       rw [shape,Hero315Frame11.ownPushes_append] at stationary
       omega
     have tag1 := no_push_unchanged [187] o1 prefixZero
     have middleReached := initialReached.append lead.trace
     have middleUnique := middleReached.boulders_nodup (by first | assumption | decide +kernel)
     have selected := lead.end_subset actualUnique U (by first | assumption | decide +kernel) (by first | assumption | decide +kernel)
     have splitBefore := lead.end_split actualUnique Others [187] (by first | assumption | decide +kernel) (by first | assumption | decide +kernel)
     change (endGroup Others o1++endGroup [187] o1).Perm (endGroup U o1) at splitBefore
     rw [tag1] at splitBefore
     cases outcome with
     | walk target => exact False.elim pays
     | push source ending =>
       obtain ⟨owner,paid⟩ := pays
       have different : source≠187 := by
         intro same
         subst source
         rw [shape,Hero315Frame11.ownPushes_append] at stationary
         simp only [tag1,ownPushes,ownPush,List.mem_cons,List.not_mem_nil,or_false,if_true] at stationary
         omega
       have ownOther : source∈endGroup Others o1 := by
         have member := splitBefore.mem_iff.mpr owner
         rcases List.mem_append.mp member with found|single
         · exact found
         · exact False.elim (different (List.mem_singleton.mp single))
       have fullTail := tail.append (Logged.cons head effect last)
       have fullShape : before++.push 187 (.stay 161)::after=
           o1++.push source ending::(o2++.push 187 (.stay 161)::after) := by
         rw [shape]
         simp only [List.append_assoc,List.cons_append]
       obtain ⟨_,adjacent,_⟩ := effect_push_data checked matched
       have inLock : source∈locks j := by
         apply Classical.byContradiction
         intro absent
         have all : source::locks j⊆endGroup U o1 := by
           intro c found
           rcases List.mem_cons.mp found with rfl|found
           · exact owner
           · exact inside found
         have large := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨absent,unique j⟩) all
         have length := endGroup_length_le U o1
         rw [List.length_cons,size j] at large
         have uSize : U.length=5 := by decide +kernel
         omega
       rcases classification j mid.player hero dir (Geometry.all_directions dir) source inLock adjacent paid with blocked|north|priced|ticket
       · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans inside selected.2) checked matched blocked)
       · exact False.elim (different north.1)
       · have one := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset priced checked matched
         have lower := event_energy_le Generated.soko1_2_potential_valid Others lead fullTail (.push source ending)
         change slack p (projectedOutcome (endGroup Others o1) (.push source ending))≤
           energy p Others (o1++.push source ending::(o2++.push 187 (.stay 161)::after)) at lower
         simp only [projectedOutcome,if_pos ownOther] at lower
         rw [←fullShape] at lower
         omega
       · obtain ⟨_,targets,clear,shift,nextHero⟩ := ticket
         have sameEnding := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset targets clear checked matched
         subst ending
         let toAfter := lead.append (Logged.cons checked matched (Logged.nil actor.state))
         have tagAfter : endGroup [187] (o1++[.push source (.stay (ticketDest source dir))])=[187] := by
           rw [endGroup_append,tag1]
           have absent : source∉([187] : List Cell) := by simpa using different
           simp only [endGroup,update,move,if_neg absent]
         have afterSplit := toAfter.end_split actualUnique Others [187] (by first | assumption | decide +kernel) (by first | assumption | decide +kernel)
         change (endGroup Others (o1++[.push source (.stay (ticketDest source dir))])++
           endGroup [187] (o1++[.push source (.stay (ticketDest source dir))])).Perm
           (endGroup U (o1++[.push source (.stay (ticketDest source dir))])) at afterSplit
         rw [tagAfter] at afterSplit
         have kept := CageFour12.shifted_inside (unique j) inside owner shift
         have pairOther : UpperAfter18712.locks (ticketIndex j source dir)⊆
             endGroup Others (o1++[.push source (.stay (ticketDest source dir))]) := by
           intro c member
           have large : c∈endGroup U (o1++[.push source (.stay (ticketDest source dir))]) := by
             simpa only [endGroup_append,endGroup] using kept member
           have both := afterSplit.mem_iff.mpr large
           rcases List.mem_append.mp both with found|single
           · exact found
           · exact False.elim (ticket_no187 j source dir ((List.mem_singleton.mp single) ▸ member))
         have afterReached := initialReached.append toAfter.trace
         have otherFacts := toAfter.end_subset actualUnique Others (by first | assumption | decide +kernel) (by first | assumption | decide +kernel)
         have heroAfter : actor.state.player∈UpperAfter18712.region (ticketIndex j source dir) := by
           rw [matches_hero mid actor (.push source (.stay (ticketDest source dir))) matched]
           exact nextHero
         have later := UpperAfter18712.owned_energy_credit UpperAfter18712.matrix fullTail afterReached
           (endGroup Others (o1++[.push source (.stay (ticketDest source dir))])) otherFacts.1 otherFacts.2 heroAfter pairOther
         rw [ticket_credit] at later
         change 2≤energy p (endGroup Others (o1++[.push source (.stay (ticketDest source dir))]))
           (o2++.push 187 (.stay 161)::after) at later
         have nn := toAfter.ownSlack_nonnegative Generated.soko1_2_potential_valid Others
         change 0≤ownSlack p Others (o1++[.push source (.stay (ticketDest source dir))]) at nn
         have fullShape' : before++.push 187 (.stay 161)::after=
             (o1++[.push source (.stay (ticketDest source dir))])++(o2++.push 187 (.stay 161)::after) := by
           rw [fullShape]
           simp only [List.append_assoc,List.cons_append,List.nil_append]
         rw [fullShape',TokenAccounting.energy_append] at othersCheap
         omega
   · obtain ⟨j,hero,inside⟩ := terminal
     have middleReached := initialReached.append first.trace
     have middleUnique := middleReached.boulders_nodup (by first | assumption | decide +kernel)
     have old := first.end_subset actualUnique U (by first | assumption | decide +kernel) (by first | assumption | decide +kernel)
     have owner : 187∈endGroup U before := by
       have mono := first.end_mono actualUnique [187] U (by first | assumption | decide +kernel) (by first | assumption | decide +kernel) (by first | assumption | decide +kernel)
       exact mono (by rw [tag];simp)
     have nextActual := step_boulders_nodup _ _ _ _ middleUnique head
     have nextUnique := GhostSubset.update_unique state t (.push 187 (.stay 161)) effect nextActual _ old.1 old.2
     have nextSubset := GhostSubset.update_subset state t (.push 187 (.stay 161)) effect _ old.1 old.2
     have kept := CageFour12.shifted_inside (unique j) inside owner (north_shift j)
     have nextReached := middleReached.append (Trace.cons head (Trace.nil t.state))
     have heroNext : t.state.player∈UpperAfter18712.region (oldIndex j) := by
       rw [matches_hero state t (.push 187 (.stay 161)) effect]
       exact north_hero j
     have later := UpperAfter18712.owned_energy_credit UpperAfter18712.matrix last nextReached
       (update (endGroup U before) (.push 187 (.stay 161))) nextUnique nextSubset heroNext kept
     have credit : UpperAfter18712.credit (oldIndex j)=2 := by
       have all : ∀ j : Fin 6,UpperAfter18712.credit (oldIndex j)=2 := by decide +kernel
       exact all j
     rw [credit] at later
     have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid U
     change 0≤ownSlack p U before at nn
     change 2≤energy p (update (endGroup U before) (.push 187 (.stay 161))) after at later
     rw [energy_at_split] at cheap
     simp only [projectedOutcome,if_pos owner] at cheap
     have one : slack p (.push 187 (.stay 161))=2 := by decide +kernel
     rw [one] at cheap
     omega
#print axioms first_north_four
end Owner1007.Upper187Start12
