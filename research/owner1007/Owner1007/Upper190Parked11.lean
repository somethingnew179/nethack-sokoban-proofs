import Owner1007.Upper190After11
import Owner1007.HeroEndSubset11
namespace Owner1007.Upper190Parked11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11

def group : List Cell := originalGroup++[188]

theorem after_west {beforeDirs middle beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_1.board middle .west=some t)
 (effect : Matches middle t (.push 190 (.stay 189)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (still137 : ownPushes [137] before=0) (still139 : ownPushes [139] before=0)
 (tag191 : endGroup [191] before=[190])
 (cheap188 : energy soko1_1.initial middle [188] before<2) :
 endGroup [191] (before++ .push 190 (.stay 189)::after)≠[] ∨
 OwnedCorral11.Good Parked18811.locks Parked18811.region t.state
   (update (endGroup group before) (.push 190 (.stay 189))) := by
  have included := end_subset_selected first (by decide) [191] originalGroup
    (by decide) (by decide) (by decide) (by decide)
  have selected190 : 190∈endGroup originalGroup before := included (by rw [tag191]; simp)
  have separate := Owner1007.Upper190Identity11.separate188 first 190 selected190
  have selected188 := first.end_subset (by decide) [188] (by decide) (by decide)
  have no189 : 189∉middle.boulders := by
    obtain ⟨result,_,push⟩ := effect_push_data checked effect
    obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear _ _ _ _ _ push).2
    have adjacent : advance soko1_1.board 190 .west=some 189 := by decide +kernel
    have destIs : dest=189 := Option.some.inj (next.symm.trans adjacent)
    exact destIs ▸ clear
  have upper1 := HeroLedger.Logged.end_append_perm first (by decide) [137] [139,191] (by decide) (by decide)
  have upper2 := HeroLedger.Logged.end_append_perm first (by decide) [139] [191] (by decide) (by decide)
  rw [no_push_unchanged _ _ still137] at upper1
  rw [no_push_unchanged _ _ still139,tag191] at upper2
  have upperPerm : (endGroup originalGroup before).Perm [137,139,190] :=
    upper1.trans ((List.Perm.refl [137]).append upper2)
  have partition := HeroLedger.Logged.end_append_perm first (by decide) originalGroup [188] (by decide) (by decide)
  have fullPerm : (endGroup group before).Perm ([137,139,190]++endGroup [188] before) :=
    partition.trans (upperPerm.append (List.Perm.refl _))
  have hero : t.state.player=190 := by rw [effect.2]
  obtain ⟨i,_,tag⟩ := Guard188Word11.guard188 Guard18811.closed first still137 still139 cheap188
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases choices with rfl|rfl|rfl|rfl|rfl|rfl
  · change endGroup [188] before=[188] at tag
    have mateBefore : 188∈middle.boulders := selected188.2 (by rw [tag]; simp)
    have inside : [188,189]⊆t.state.boulders := by
      rw [effect.2]
      intro c found
      simp only [List.mem_cons,List.not_mem_nil,or_false] at found
      rcases found with rfl|rfl
      · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide : 188≠190)).mpr mateBefore)
      · simp
    have fixed := locked_identity last
      (Owner1007.locked_of_check soko1_1.board [188,189] (by decide +kernel)) inside (by simp : 189∈[188,189])
    apply Or.inl
    rw [endGroup_append,tag191]
    change endGroup [189] after≠[]
    rw [fixed]
    simp
  · change endGroup [188] before=[189] at tag
    exact False.elim (no189 (selected188.2 (by rw [tag]; simp)))
  · change endGroup [188] before=[190] at tag
    exact False.elim (separate (by rw [tag]; simp))
  · change endGroup [188] before=[164] at tag
    have beforePerm : (endGroup group before).Perm ([137,139,190]++[164]) := by
      simpa only [tag] using fullPerm
    have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
    have concrete : (update ([137,139,190]++[164]) (.push 190 (.stay 189))).Perm
        (Parked18811.locks ⟨0,by decide⟩) := by decide +kernel
    have linked := afterPerm.trans concrete
    refine Or.inr ⟨⟨0,by decide⟩,?_,?_⟩
    · rw [hero]; decide +kernel
    · exact fun _ found => linked.mem_iff.mpr found

  · change endGroup [188] before=[138] at tag
    have beforePerm : (endGroup group before).Perm ([137,139,190]++[138]) := by
      simpa only [tag] using fullPerm
    have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
    have concrete : (update ([137,139,190]++[138]) (.push 190 (.stay 189))).Perm
        (Parked18811.locks ⟨1,by decide⟩) := by decide +kernel
    have linked := afterPerm.trans concrete
    refine Or.inr ⟨⟨1,by decide⟩,?_,?_⟩
    · rw [hero]; decide +kernel
    · exact fun _ found => linked.mem_iff.mpr found

  · change endGroup [188] before=[112] at tag
    have beforePerm : (endGroup group before).Perm ([137,139,190]++[112]) := by
      simpa only [tag] using fullPerm
    have afterPerm := update_perm beforePerm (.push 190 (.stay 189))
    have concrete : (update ([137,139,190]++[112]) (.push 190 (.stay 189))).Perm
        (Parked18811.locks ⟨2,by decide⟩) := by decide +kernel
    have linked := afterPerm.trans concrete
    refine Or.inr ⟨⟨2,by decide⟩,?_,?_⟩
    · rw [hero]; decide +kernel
    · exact fun _ found => linked.mem_iff.mpr found

#print axioms after_west
end Owner1007.Upper190Parked11
