import Owner1007.RightEntry12
import Owner1007.RightEntryCapacity12
import Owner1007.NorthBound12

namespace Owner1007.RightEntry12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem member_of_tight {K group : List Cell} (uniqueK : K.Nodup) (inside : K⊆group)
 (count : group.length≤K.length) {cell : Cell} (member : cell∈group) : cell∈K := by
 by_cases present : cell∈K
 · exact present
 · have unique : (cell::K).Nodup := List.nodup_cons.mpr ⟨present,uniqueK⟩
   have both : cell::K⊆group := by
     intro c h
     rcases List.mem_cons.mp h with equal | h
     · subst c
       exact member
     · exact inside h
   have bound := List.Nodup.length_le_of_subset unique both
   simp only [List.length_cons] at bound
   omega

theorem slack271_at245 (before : List Outcome) (same : endGroup [271] before=[245]) :
 1≤ownSlack p [271] before := by
 have survives : endGroup [271] before≠[] := by rw [same]; simp
 have ledger := survivor_energy p 271 before survives
 have positive : 1≤ownPushes [271] before := by
   by_cases zero : ownPushes [271] before=0
   · have fixed := no_push_unchanged [271] before zero
     rw [same] at fixed
     exact False.elim ((by decide +kernel : ([245]:List Cell)≠[271]) fixed)
   · omega
 unfold energy at ledger
 rw [same] at ledger
 have a : p.boulder 271=0 := by decide +kernel
 have b : debtOf p [245]=0 := by decide +kernel
 rw [a,b] at ledger
 simp only [Int.neg_zero,Int.zero_add,Int.ofNat_eq_natCast] at ledger
 omega

theorem right_five
 (matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true)
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (player : state.player=296) (inside : locks 0⊆state.boulders) (completed : Goal final) :
 5≤energy p RightEnergy12.Right outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have rightInside := List.Subset.trans start_right inside
 rcases TaggedFlow12.event_or_good closed unique tag_inside tag_sound tag_update
   logged reached (locks 0) [271] [246] (unique 0) inside
   (i:=0) (by rw [player]; exact start_hero) (fun _ h=>h) rfl rfl with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locksOne,pays,sAt,tAt,unchanged⟩ :=
     event.split_fixed fixed fixed_inside fixed_guard reached (unique 0) inside
   have middleReached := reached.append first.trace
   have middleUnique := middleReached.boulders_nodup (by decide +kernel)
   have oldGroup := first.end_subset actualUnique (locks 0) (unique 0) inside
   have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
   have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual
     (endGroup (locks 0) before) oldGroup.1 oldGroup.2
   have nextSubset := GhostSubset.update_subset middle t outcome effect
     (endGroup (locks 0) before) oldGroup.1 oldGroup.2
   have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
   cases outcome with
   | walk target => exact False.elim pays
   | push source ending =>
     obtain ⟨owner,pays⟩ := pays
     obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
     have count := endGroup_length_le (locks 0) before
     rw [sizes 0] at count
     have sourceInside : source∈locks j :=
       member_of_tight (unique j) locksOne (by rw [sizes j]; exact count) owner
     have cases := head_classification j middle.player heroBefore dir source sourceInside adjacent pays
     rcases cases with dead | moved | frozen
     · obtain ⟨rfl,rfl,rfl⟩ := dead
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 271 .east=[272] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have prior : endGroup [271] before=[271] := by simpa only [show tagS (1:Fin 4)=271 by decide +kernel] using sAt
       have stepPrice : slack p (.push 271 (.stay 272))=1 := by decide +kernel
       have bound := event_energy_le Generated.soko1_2_potential_valid [271] first last (.push 271 (.stay 272))
       rw [prior] at bound
       change slack p (.push 271 (.stay 272))≤energy p [271] (before++(.push 271 (.stay 272))::after) at bound
       have ticket : (1:Int)≤energy p [271] outcomes := by rw [shape]; omega
       have shapeNext : t.state.boulders=272::middle.boulders.erase 271 := by
         simpa only [Matches] using congrArg (fun h : Transition=>h.state.boulders) effect.2
       have present : (272:Cell)∈t.state.boulders := by rw [shapeNext]; simp
       have alive := NorthBound12.after_park_survives last nextActual 271 272 present locked272 before prior
       have survives : endGroup [271] outcomes≠[] := by rw [shape]; exact alive
       exact RightEntryCapacity12.five_of_dead271 logged reached player rightInside completed survives ticket
     · obtain ⟨rfl,rfl,stage⟩ := moved
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 246 .north=[220] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have tagEq : tagS j=245 := by rcases stage with rfl|rfl <;> decide +kernel
       have priorS : endGroup [271] before=[245] := by simpa only [tagEq] using sAt
       have priorT : endGroup [246] before=[246] := by simpa only [tagT] using tAt
       have oneS := slack271_at245 before priorS
       have later := last.energy_nonnegative Generated.soko1_2_potential_valid [245]
       change 0≤energy p [245] after at later
       have ticketS : (1:Int)≤energy p [271] outcomes := by
         rw [shape,energy_at_split,priorS]
         change 1≤ownSlack p [271] before+0+energy p [245] after
         omega
       have stepPrice : slack p (.push 246 (.stay 220))=1 := by decide +kernel
       have bound := event_energy_le Generated.soko1_2_potential_valid [246] first last (.push 246 (.stay 220))
       rw [priorT] at bound
       change slack p (.push 246 (.stay 220))≤energy p [246] (before++(.push 246 (.stay 220))::after) at bound
       have ticketT : (1:Int)≤energy p [246] outcomes := by rw [shape]; omega
       exact RightEntryCapacity12.five_of_both logged reached player rightInside completed ticketT ticketS
     · obtain ⟨rfl,rfl,shift⟩ := frozen
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 245 .north=[219] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := CageFour12.shifted_inside (unique j) locksOne owner shift
       have survives := last.locked_end_inside nextActual
         (update (endGroup (locks 0) before) (.push 245 (.stay 219))) nextUnique nextSubset
         [192,193,218,219] lockedSquare kept
       have finalInside := last.end_subset nextActual
         (update (endGroup (locks 0) before) (.push 245 (.stay 219))) nextUnique nextSubset
       have count := List.Nodup.length_le_of_subset (show ([192,193,218,219]:List Cell).Nodup by decide +kernel)
         (List.Subset.trans survives finalInside.2)
       rw [RightEntryCapacity12.final_two logged reached completed] at count
       change 4≤2 at count
       omega
 · obtain ⟨j,hero,locksOne,_,_⟩ := terminal
   have finalInside := logged.end_subset actualUnique (locks 0) (unique 0) inside
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans locksOne finalInside.2)
   rw [sizes j,RightEntryCapacity12.final_two logged reached completed] at count
   omega
#print axioms right_five
end Owner1007.RightEntry12

