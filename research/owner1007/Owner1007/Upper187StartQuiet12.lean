import Owner1007.Upper187StartNorth12
namespace Owner1007.Upper187StartQuiet12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.Upper187FirstGeometry12
open Owner1007.Upper187Start12 (U Others)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem prefix_good
 {initial : State} {initialDirs : List Dir} {initialPushes initialMoves : Nat}
 (initialReached : Trace soko1_2.board soko1_2.initial initialDirs initial initialPushes initialMoves)
 (uInside : U⊆initial.boulders) (heroInitial : initial.player∈Upper187FirstGeometry12.region 0)
 {beforeDirs state beforePushes beforeMoves before afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_2.board initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_2.board state afterDirs final afterPushes afterMoves after)
 (stationary : ownPushes [187] before=0)
 (othersCheap : energy p Others (before++after)<2) :
 ∃ j : Fin 6,state.player∈region j ∧locks j⊆endGroup U before := by
 have actualUnique := initialReached.boulders_nodup (by first | assumption | decide +kernel)
 have othersInside : Others⊆initial.boulders := List.Subset.trans (by decide +kernel : Others⊆U) uInside
 have singletonInside : ([187]:List Cell)⊆initial.boulders := List.Subset.trans (by decide +kernel : ([187]:List Cell)⊆U) uInside
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
     have fullTail := tail.append last
     have fullShape : before++after=
         o1++.push source ending::(o2++after) := by
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
         energy p Others (o1++.push source ending::(o2++after)) at lower
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
         (o2++after) at later
       have nn := toAfter.ownSlack_nonnegative Generated.soko1_2_potential_valid Others
       change 0≤ownSlack p Others (o1++[.push source (.stay (ticketDest source dir))]) at nn
       have fullShape' : before++after=
           (o1++[.push source (.stay (ticketDest source dir))])++(o2++after) := by
         rw [fullShape]
         simp only [List.append_assoc,List.cons_append,List.nil_append]
       rw [fullShape',TokenAccounting.energy_append] at othersCheap
       omega
 · exact terminal
#print axioms prefix_good

theorem south_impossible : ∀ i,∀ hero∈region i,
 advance soko1_2.board hero .south=some 187→False := by decide +kernel

theorem first_south_others_two
 {initial : State} {initialDirs : List Dir} {initialPushes initialMoves : Nat}
 (initialReached : Trace soko1_2.board soko1_2.initial initialDirs initial initialPushes initialMoves)
 (uInside : U⊆initial.boulders) (heroInitial : initial.player∈Upper187FirstGeometry12.region 0)
 {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_2.board initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_2.board state .south=some t) (effect : Matches state t (.push 187 (.stay 213)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (stationary : ownPushes [187] before=0) :
 2≤energy p Others (before++.push 187 (.stay 213)::after) := by
 apply Classical.byContradiction
 intro wrong
 have cheap : energy p Others (before++.push 187 (.stay 213)::after)<2 := by omega
 obtain ⟨i,hero,_⟩ := prefix_good initialReached uInside heroInitial first (Logged.cons head effect last) stationary cheap
 obtain ⟨_,adjacent,_⟩ := effect_push_data head effect
 exact south_impossible i state.player hero adjacent
#print axioms first_south_others_two
theorem south_original_energy_zero
 {initial : State} {initialDirs : List Dir} {initialPushes initialMoves : Nat}
 (initialReached : Trace soko1_2.board soko1_2.initial initialDirs initial initialPushes initialMoves)
 (uInside : U⊆initial.boulders) (heroInitial : initial.player∈Upper187FirstGeometry12.region 0)
 {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_2.board initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_2.board state .south=some t) (effect : Matches state t (.push 187 (.stay 213)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (stationary : ownPushes [187] before=0)
 (small : energy p U (before++.push 187 (.stay 213)::after)≤2) :
 energy p [187] (before++.push 187 (.stay 213)::after)=0 := by
 have actualUnique := initialReached.boulders_nodup (by first | assumption | decide +kernel)
 have other := first_south_others_two initialReached uInside heroInitial first head effect last stationary
 let whole := first.append (Logged.cons head effect last)
 have split := whole.energy_split (by first | assumption | decide +kernel) p Others [187] (by first | assumption | decide +kernel) (by first | assumption | decide +kernel)
 change energy p U (before++.push 187 (.stay 213)::after)=
   energy p Others (before++.push 187 (.stay 213)::after)+energy p [187] (before++.push 187 (.stay 213)::after) at split
 have nn := whole.energy_nonnegative Generated.soko1_2_potential_valid [187]
 change 0≤energy p [187] (before++.push 187 (.stay 213)::after) at nn
 omega
#print axioms south_original_energy_zero
end Owner1007.Upper187StartQuiet12
