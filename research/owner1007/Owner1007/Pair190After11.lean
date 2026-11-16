import Owner1007.PairFirstCut11
import Owner1007.Guard188OneWord11
import Owner1007.Upper190Identity11
import Owner1007.Pair137Energy11
import Owner1007.ParkedThree11Data
namespace Owner1007.Pair190After11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition NetHack.Sokoban.LowerBounds
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.PairFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev Cut {dirs final pushes moves outcomes} :=
 UpperFirstCut11.FirstCut PairPath11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes

theorem stationary139_before190 {dirs final pushes moves outcomes}
 (cut : Cut (dirs:=dirs) (final:=final) (pushes:=pushes) (moves:=moves) (outcomes:=outcomes))
 (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.west) :
 ownPushes [139] cut.beforeOutcomes=0 := by
 have good := quiet_good PairPath11.closed PairPath11.unique PairPath11.size cut.before (by decide) (by decide) (by decide) (by decide)
   initial_good (by simp)
 obtain ⟨i,heroInside,locksInside⟩ := good
 obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
 have sourceIs : source=190 := Option.some.inj (metadata.symm.trans sourceEq)
 have selected190 : 190∈endGroup originalGroup cut.beforeOutcomes := sourceIs ▸ owner
 have bounded := endGroup_length_le originalGroup cut.beforeOutcomes
 have member := lock_complete i _ bounded locksInside 190 selected190
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [directionEq] using cut.headChecked
 have hero := ActorPrices11.support_of_check 190 cut.middle.player .west 191 (by decide +kernel)
   (step_player_clear _ _ _ _ checked).1 (Pair137Energy11.west_support checked sourceEq)
 have inRegion : 191∈PairPath11.region i := by simpa only [hero] using heroInside
 have checked139 : (List.finRange 9).all (fun i => decide
   (190∈PairPath11.locks i → 191∈PairPath11.region i → 139∈PairPath11.locks i))=true := by decide +kernel
 have present139 := of_decide_eq_true (List.all_eq_true.mp checked139 i (by simp)) member inRegion
 exact stationary_source cut 139 (by decide) (locksInside present139)

def group : List Cell := originalGroup++[188]

theorem after_190west {dirs final pushes moves outcomes}
 (cut : Cut (dirs:=dirs) (final:=final) (pushes:=pushes) (moves:=moves) (outcomes:=outcomes))
 (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.west)
 (effect : Matches cut.middle cut.actor (.push 190 (.stay 189)))
 (cheap188 : energy soko1_1.initial cut.middle [188] cut.beforeOutcomes<2) :
 endGroup [191] outcomes≠[] ∨
 OwnedCorral11.Good ParkedThree11.locks ParkedThree11.region cut.actor.state
   (update (endGroup group cut.beforeOutcomes) cut.headOutcome) := by
 have headEq := GhostProjection.matches_unique cut.middle cut.actor cut.headOutcome (.push 190 (.stay 189)) cut.headEffect effect
 rw [headEq]
 have still139 := stationary139_before190 cut sourceEq directionEq
 obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
 have sourceIs : source=190 := Option.some.inj (metadata.symm.trans sourceEq)
 have selected190 : 190∈endGroup originalGroup cut.beforeOutcomes := sourceIs ▸ owner
 have pairParts := HeroLedger.Logged.end_append_perm cut.before.logged (by decide) [139] [191] (by decide) (by decide)
 rw [no_push_unchanged _ _ still139] at pairParts
 have tagMember : 190∈endGroup [191] cut.beforeOutcomes := by
   simpa using pairParts.mem_iff.mp selected190
 have tag191 := Upper190Identity11.singleton_member _ 190 (Nat.le_trans (endGroup_length_le [191] cut.beforeOutcomes) (by simp)) tagMember
 have pairPerm : (endGroup originalGroup cut.beforeOutcomes).Perm [139,190] := by
   simpa [PairFirstCut11.originalGroup,tag191] using pairParts
 have partition := HeroLedger.Logged.end_append_perm cut.before.logged (by decide) originalGroup [188] (by decide) (by decide)
 have fullPerm : (endGroup group cut.beforeOutcomes).Perm ([139,190]++endGroup [188] cut.beforeOutcomes) :=
   partition.trans (pairPerm.append (List.Perm.refl _))
 have allSelected := cut.before.logged.end_subset (by decide) group (by decide) (by decide)
 have disjoint := (List.nodup_append.mp (partition.nodup_iff.mp allSelected.1)).2.2
 have separate : 190∉endGroup [188] cut.beforeOutcomes := by
   intro member
   exact disjoint 190 selected190 190 member rfl
 have selected188 := cut.before.logged.end_subset (by decide) [188] (by decide) (by decide)
 have no189 : 189∉cut.middle.boulders := by
   obtain ⟨result,_,push⟩ := effect_push_data cut.headChecked effect
   obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear _ _ _ _ _ push).2
   have adjacent : advance soko1_1.board 190 cut.direction=some 189 := by rw [directionEq]; decide +kernel
   have destIs : dest=189 := Option.some.inj (next.symm.trans adjacent)
   exact destIs ▸ clear
 have hero : cut.actor.state.player=190 := by rw [effect.2]
 obtain ⟨i,_,tag⟩ := Guard188OneWord11.guard188 Guard188One11.closed cut.before.logged still139 cheap188
 obtain ⟨i,bound⟩ := i
 have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl
 · change endGroup [188] cut.beforeOutcomes=[188] at tag
   have mateBefore : 188∈cut.middle.boulders := selected188.2 (by rw [tag]; simp)
   have inside : [188,189]⊆cut.actor.state.boulders := by
     rw [effect.2]
     intro c found
     simp only [List.mem_cons,List.not_mem_nil,or_false] at found
     rcases found with rfl|rfl
     · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide : 188≠190)).mpr mateBefore)
     · simp
   have fixed := locked_identity cut.after (Owner1007.locked_of_check soko1_1.board [188,189] (by decide +kernel))
     inside (by simp : 189∈[188,189])
   have allEffects := cut.outcomesEq
   rw [headEq] at allEffects
   apply Or.inl
   rw [allEffects,endGroup_append,tag191]
   change endGroup [189] cut.afterOutcomes≠[]
   rw [fixed]
   simp
 · change endGroup [188] cut.beforeOutcomes=[189] at tag
   exact False.elim (no189 (selected188.2 (by rw [tag]; simp)))
 · change endGroup [188] cut.beforeOutcomes=[190] at tag
   exact False.elim (separate (by rw [tag]; simp))

 · change endGroup [188] cut.beforeOutcomes=[164] at tag
   have beforePerm : (endGroup group cut.beforeOutcomes).Perm ([139,190]++[164]) := by
     simpa only [tag] using fullPerm
   have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
   have concrete : (update ([139,190]++[164]) (.push 190 (.stay 189))).Perm
       (ParkedThree11.locks ⟨0,by decide⟩) := by decide +kernel
   have linked := afterPerm.trans concrete
   refine Or.inr ⟨⟨0,by decide⟩,?_,?_⟩
   · rw [hero]; decide +kernel
   · exact fun _ found => linked.mem_iff.mpr found

 · change endGroup [188] cut.beforeOutcomes=[138] at tag
   have beforePerm : (endGroup group cut.beforeOutcomes).Perm ([139,190]++[138]) := by
     simpa only [tag] using fullPerm
   have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
   have concrete : (update ([139,190]++[138]) (.push 190 (.stay 189))).Perm
       (ParkedThree11.locks ⟨1,by decide⟩) := by decide +kernel
   have linked := afterPerm.trans concrete
   refine Or.inr ⟨⟨1,by decide⟩,?_,?_⟩
   · rw [hero]; decide +kernel
   · exact fun _ found => linked.mem_iff.mpr found

 · change endGroup [188] cut.beforeOutcomes=[112] at tag
   have beforePerm : (endGroup group cut.beforeOutcomes).Perm ([139,190]++[112]) := by
     simpa only [tag] using fullPerm
   have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
   have concrete : (update ([139,190]++[112]) (.push 190 (.stay 189))).Perm
       (ParkedThree11.locks ⟨2,by decide⟩) := by decide +kernel
   have linked := afterPerm.trans concrete
   refine Or.inr ⟨⟨2,by decide⟩,?_,?_⟩
   · rw [hero]; decide +kernel
   · exact fun _ found => linked.mem_iff.mpr found

#print axioms after_190west
end Owner1007.Pair190After11
