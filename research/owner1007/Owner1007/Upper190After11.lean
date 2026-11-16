import Owner1007.Guard188Word11
import Owner1007.Upper190Identity11
import Owner1007.Parked18811
import Owner1007.HeroEnergyTrace11
namespace Owner1007.Upper190After11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11

def group : List Cell := originalGroup++[188]

theorem FirstCut.after_190west {dirs final pushes moves outcomes}
    (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
    (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.west)
    (effect : Matches cut.middle cut.actor (.push 190 (.stay 189)))
    (cheap188 : energy soko1_1.initial cut.middle [188] cut.beforeOutcomes<2) :
    endGroup [191] outcomes≠[] ∨
      OwnedCorral11.Good Parked18811.locks Parked18811.region cut.actor.state
        (update (endGroup group cut.beforeOutcomes) cut.headOutcome) := by
  have headEq := GhostProjection.matches_unique cut.middle cut.actor cut.headOutcome
    (.push 190 (.stay 189)) cut.headEffect effect
  rw [headEq]
  obtain ⟨still137,still139⟩ := Owner1007.Upper190History11.FirstCut.stationary_before_190west cut sourceEq directionEq
  have tag191 := Owner1007.Upper190Identity11.FirstCut.original191_at190 cut sourceEq directionEq
  obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
  have sourceIs : source=190 := Option.some.inj (metadata.symm.trans sourceEq)
  have selected190 : 190∈endGroup originalGroup cut.beforeOutcomes := sourceIs ▸ owner
  have separate := Owner1007.Upper190Identity11.separate188 cut.before.logged 190 selected190
  have selected188 := cut.before.logged.end_subset (by decide) [188] (by decide) (by decide)
  have no189 : 189∉cut.middle.boulders := by
    obtain ⟨result,_,push⟩ := effect_push_data cut.headChecked effect
    obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear _ _ _ _ _ push).2
    have adjacent : advance soko1_1.board 190 cut.direction=some 189 := by rw [directionEq]; decide +kernel
    have destIs : dest=189 := Option.some.inj (next.symm.trans adjacent)
    exact destIs ▸ clear
  have upper1 := HeroLedger.Logged.end_append_perm cut.before.logged (by decide) [137] [139,191] (by decide) (by decide)
  have upper2 := HeroLedger.Logged.end_append_perm cut.before.logged (by decide) [139] [191] (by decide) (by decide)
  rw [no_push_unchanged _ _ still137] at upper1
  rw [no_push_unchanged _ _ still139,tag191] at upper2
  have upperPerm : (endGroup originalGroup cut.beforeOutcomes).Perm [137,139,190] :=
    upper1.trans ((List.Perm.refl [137]).append upper2)
  have partition := HeroLedger.Logged.end_append_perm cut.before.logged (by decide) originalGroup [188] (by decide) (by decide)
  have fullPerm : (endGroup group cut.beforeOutcomes).Perm ([137,139,190]++endGroup [188] cut.beforeOutcomes) :=
    partition.trans (upperPerm.append (List.Perm.refl _))
  have hero : cut.actor.state.player=190 := by rw [effect.2]
  obtain ⟨i,_,tag⟩ := Guard188Word11.guard188 Guard18811.closed cut.before.logged still137 still139 cheap188
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
    have fixed := locked_identity cut.after
      (Owner1007.locked_of_check soko1_1.board [188,189] (by decide +kernel)) inside (by simp : 189∈[188,189])
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
    have beforePerm : (endGroup group cut.beforeOutcomes).Perm ([137,139,190]++[164]) := by
      simpa only [tag] using fullPerm
    have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
    have concrete : (update ([137,139,190]++[164]) (.push 190 (.stay 189))).Perm
        (Parked18811.locks ⟨0,by decide⟩) := by decide +kernel
    have linked := afterPerm.trans concrete
    refine Or.inr ⟨⟨0,by decide⟩,?_,?_⟩
    · rw [hero]; decide +kernel
    · exact fun _ found => linked.mem_iff.mpr found

  · change endGroup [188] cut.beforeOutcomes=[138] at tag
    have beforePerm : (endGroup group cut.beforeOutcomes).Perm ([137,139,190]++[138]) := by
      simpa only [tag] using fullPerm
    have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
    have concrete : (update ([137,139,190]++[138]) (.push 190 (.stay 189))).Perm
        (Parked18811.locks ⟨1,by decide⟩) := by decide +kernel
    have linked := afterPerm.trans concrete
    refine Or.inr ⟨⟨1,by decide⟩,?_,?_⟩
    · rw [hero]; decide +kernel
    · exact fun _ found => linked.mem_iff.mpr found

  · change endGroup [188] cut.beforeOutcomes=[112] at tag
    have beforePerm : (endGroup group cut.beforeOutcomes).Perm ([137,139,190]++[112]) := by
      simpa only [tag] using fullPerm
    have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
    have concrete : (update ([137,139,190]++[112]) (.push 190 (.stay 189))).Perm
        (Parked18811.locks ⟨2,by decide⟩) := by decide +kernel
    have linked := afterPerm.trans concrete
    refine Or.inr ⟨⟨2,by decide⟩,?_,?_⟩
    · rw [hero]; decide +kernel
    · exact fun _ found => linked.mem_iff.mpr found

#print axioms FirstCut.after_190west
end Owner1007.Upper190After11
