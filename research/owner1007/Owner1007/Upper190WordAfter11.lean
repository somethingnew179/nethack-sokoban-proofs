import Owner1007.PairPost11
import Owner1007.Guard188FourWord11
import Owner1007.Upper190After11
import Owner1007.Upper190Identity11
import Owner1007.Upper187Cover11
namespace Owner1007.Upper190WordAfter11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem after190west {dirs final pushes moves outcomes}
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.west)
 (effect : Matches cut.middle cut.actor (.push 190 (.stay 189)))
 (budget : energy soko1_1.initial cut.middle Guard188FourWord11.G cut.beforeOutcomes<4) :
 endGroup [191] outcomes≠[] ∨
 (2≤energy soko1_1.initial cut.middle Guard188FourWord11.G cut.beforeOutcomes ∧
   OwnedCorral11.Good Upper187Cover11.locks Upper187Cover11.region cut.actor.state
     (update (endGroup Upper190After11.group cut.beforeOutcomes) cut.headOutcome)) ∨
 OwnedCorral11.Good Parked18811.locks Parked18811.region cut.actor.state
   (update (endGroup Upper190After11.group cut.beforeOutcomes) cut.headOutcome) := by
 have headEq := GhostProjection.matches_unique cut.middle cut.actor cut.headOutcome (.push 190 (.stay 189)) cut.headEffect effect
 rw [headEq]
 obtain ⟨still137,still139⟩ := Upper190History11.FirstCut.stationary_before_190west cut sourceEq directionEq
 have tag191 := Upper190Identity11.FirstCut.original191_at190 cut sourceEq directionEq
 obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
 have sourceIs : source=190 := Option.some.inj (metadata.symm.trans sourceEq)
 have selected190 : 190∈endGroup originalGroup cut.beforeOutcomes := sourceIs ▸ owner
 have separate := Upper190Identity11.separate188 cut.before.logged 190 selected190
 have selected188 := cut.before.logged.end_subset (by decide) [188] (by decide) (by decide)
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [directionEq] using cut.headChecked
 have no189 : 189∉cut.middle.boulders := by
   obtain ⟨result,_,push⟩ := effect_push_data checked effect
   obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear _ _ _ _ _ push).2
   have same : dest=189 := Option.some.inj (next.symm.trans (show advance soko1_1.board 190 .west=some 189 by decide +kernel))
   exact same ▸ clear
 have beforeHero := ActorPrices11.support_of_check 190 cut.middle.player .west 191 (by decide +kernel)
   (step_player_clear _ _ _ _ checked).1 (PairPost11.source_adjacent checked sourceEq)
 have no191 : 191∉cut.middle.boulders := by
   have clear := (step_player_clear _ _ _ _ checked).2.2.1
   simpa only [beforeHero] using clear
 have upper1 := HeroLedger.Logged.end_append_perm cut.before.logged (by decide) [137] [139,191] (by decide) (by decide)
 have upper2 := HeroLedger.Logged.end_append_perm cut.before.logged (by decide) [139] [191] (by decide) (by decide)
 rw [no_push_unchanged _ _ still137] at upper1
 rw [no_push_unchanged _ _ still139,tag191] at upper2
 have upperPerm : (endGroup originalGroup cut.beforeOutcomes).Perm [137,139,190] :=
   upper1.trans ((List.Perm.refl [137]).append upper2)
 have partition := HeroLedger.Logged.end_append_perm cut.before.logged (by decide) originalGroup [188] (by decide) (by decide)
 have fullPerm : (endGroup Upper190After11.group cut.beforeOutcomes).Perm ([137,139,190]++endGroup [188] cut.beforeOutcomes) :=
   partition.trans (upperPerm.append (List.Perm.refl _))
 have hero : cut.actor.state.player=190 := by rw [effect.2]
 obtain ⟨i,_,tag⟩ := Guard188FourWord11.word cut.before.logged still137 still139 budget
 obtain ⟨i,bound⟩ := i
 have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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
   have beforePerm : (endGroup Upper190After11.group cut.beforeOutcomes).Perm ([137,139,190]++[164]) := by
     simpa only [tag] using fullPerm
   have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
   have concrete : (update ([137,139,190]++[164]) (.push 190 (.stay 189))).Perm (Parked18811.locks ⟨0,by decide⟩) := by decide +kernel
   have linked := afterPerm.trans concrete
   refine Or.inr (Or.inr ⟨⟨0,by decide⟩,?_,?_⟩)
   · rw [hero]; decide +kernel
   · exact fun _ found => linked.mem_iff.mpr found

 · change endGroup [188] cut.beforeOutcomes=[138] at tag
   have beforePerm : (endGroup Upper190After11.group cut.beforeOutcomes).Perm ([137,139,190]++[138]) := by
     simpa only [tag] using fullPerm
   have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
   have concrete : (update ([137,139,190]++[138]) (.push 190 (.stay 189))).Perm (Parked18811.locks ⟨1,by decide⟩) := by decide +kernel
   have linked := afterPerm.trans concrete
   refine Or.inr (Or.inr ⟨⟨1,by decide⟩,?_,?_⟩)
   · rw [hero]; decide +kernel
   · exact fun _ found => linked.mem_iff.mpr found

 · change endGroup [188] cut.beforeOutcomes=[112] at tag
   have beforePerm : (endGroup Upper190After11.group cut.beforeOutcomes).Perm ([137,139,190]++[112]) := by
     simpa only [tag] using fullPerm
   have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
   have concrete : (update ([137,139,190]++[112]) (.push 190 (.stay 189))).Perm (Parked18811.locks ⟨2,by decide⟩) := by decide +kernel
   have linked := afterPerm.trans concrete
   refine Or.inr (Or.inr ⟨⟨2,by decide⟩,?_,?_⟩)
   · rw [hero]; decide +kernel
   · exact fun _ found => linked.mem_iff.mpr found

 · change endGroup [188] cut.beforeOutcomes=[187] at tag
   have paid := Guard188FourWord11.prefix_two_of_marker cut.before.logged still137 still139 budget 187 (by decide) tag
   have beforePerm : (endGroup Upper190After11.group cut.beforeOutcomes).Perm ([137,139,190]++[187]) := by
     simpa only [tag] using fullPerm
   have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
   have concrete : (update ([137,139,190]++[187]) (.push 190 (.stay 189))).Perm (Upper187Cover11.locks ⟨0,by decide⟩) := by decide +kernel
   have linked := afterPerm.trans concrete
   refine Or.inr (Or.inl ⟨paid,⟨⟨0,by decide⟩,?_,?_⟩⟩)
   · rw [hero]; decide +kernel
   · exact fun _ found => linked.mem_iff.mpr found
 · change endGroup [188] cut.beforeOutcomes=[191] at tag
   exact False.elim (no191 (selected188.2 (by rw [tag]; simp)))
#print axioms after190west
end Owner1007.Upper190WordAfter11
