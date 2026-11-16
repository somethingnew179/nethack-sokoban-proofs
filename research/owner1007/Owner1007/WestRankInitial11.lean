import Owner1007.WestRank11Data
import Owner1007.UpperResetHistory11
import Owner1007.PairPost11
import Owner1007.Upper190Identity11
namespace Owner1007.WestRankInitial11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem canonical_group (i : Fin 19) (group : List Cell) (unique : group.Nodup) (bounded : group.length≤3)
 (inside : UpperZero11.locks i⊆group) : group.Perm (UpperZero11.locks i) := by
 apply (List.perm_ext_iff_of_nodup unique (UpperZero11.unique i)).mpr
 intro cell
 constructor
 · intro member
   by_cases known : cell∈UpperZero11.locks i
   · exact known
   · have all : cell::UpperZero11.locks i⊆group := by
       intro c found
       rcases List.mem_cons.mp found with rfl|later
       · exact member
       · exact inside later
     have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨known,UpperZero11.unique i⟩) all
     simp only [List.length_cons,UpperZero11.size i] at card
     omega
 · exact fun h => inside h

theorem after138west {dirs final pushes moves outcomes}
 (cut : UpperFirstCut11.FirstCut UpperZero11.paid soko1_1.initial UpperFirstCut11.originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 138) (directionEq : cut.direction=.west)
 (effect : Matches cut.middle cut.actor (.push 138 (.stay 137)))
 (cheap137 : energy soko1_1.initial final [137] outcomes<2) :
 ∃i : Fin 15, cut.actor.state.player∈WestRank11.region i ∧
   WestRank11.locks i⊆update (endGroup UpperFirstCut11.originalGroup cut.beforeOutcomes) cut.headOutcome ∧
   update (endGroup [137] cut.beforeOutcomes) cut.headOutcome=[WestRank11.marker i] ∧
   WestRank11.rank i=0 ∧ ownPushes [191] cut.beforeOutcomes=0 := by
 have ownerPair := UpperResetHistory11.head_pair_owned cut sourceEq (by simp [CutActor11.Exit,directionEq]) cheap137
 have pays : OwnedCorral11.PaidStep PairPath11.paid (endGroup PairFirstCut11.originalGroup cut.beforeOutcomes) cut.direction cut.actor :=
   ⟨138,ownerPair,sourceEq,by simp [PairPath11.paid,directionEq]⟩
 let pairCut := UpperToPair11.as_pair cut pays
 have pairPerm := (PairPost11.before_after (support:=139) (source:=138) (landing:=137) (dir:=.west)
   (old:=[138,191]) (next:=[137,191]) pairCut (by simp [PairPost11.edges]) sourceEq directionEq effect).1
 have selected191 : 191∈endGroup PairFirstCut11.originalGroup cut.beforeOutcomes := pairPerm.mem_iff.mpr (by simp)
 have still191 := PairFirstCut11.stationary_source pairCut 191 (by decide) selected191
 have good := UpperFirstCut11.quiet_good UpperZero11.closed cut.before (by decide) (by decide) (by decide) (by decide)
   UpperFirstCut11.original_good (by simp)
 obtain ⟨i,heroInside,locksInside⟩ := good
 have selected := cut.before.logged.end_subset (by decide) UpperFirstCut11.originalGroup (by decide) (by decide)
 have bounded := endGroup_length_le UpperFirstCut11.originalGroup cut.beforeOutcomes
 have upperPerm := canonical_group i _ selected.1 bounded locksInside
 obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
 have sourceIs : source=138 := Option.some.inj (metadata.symm.trans sourceEq)
 have selected138 : 138∈endGroup UpperFirstCut11.originalGroup cut.beforeOutcomes := sourceIs ▸ owner
 have member138 := UpperQuiet11.lock_complete i _ bounded locksInside 138 selected138
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [directionEq] using cut.headChecked
 have hero := ActorPrices11.support_of_check 138 cut.middle.player .west 139 (by decide +kernel)
   (step_player_clear _ _ _ _ checked).1 (PairPost11.source_adjacent checked sourceEq)
 have no137 : 137∉cut.middle.boulders := by
   obtain ⟨result,_,push⟩ := effect_push_data checked effect
   obtain ⟨dest,next,_,_,empty⟩ := (push_first_clear _ _ _ _ _ push).2
   have same : dest=137 := Option.some.inj (next.symm.trans (show advance soko1_1.board 138 .west=some 137 by decide +kernel))
   exact same ▸ empty
 have noLock137 : 137∉UpperZero11.locks i := fun found => no137 (selected.2 (locksInside found))
 have hero139 : 139∈UpperZero11.region i := by simpa only [hero] using heroInside
 have possible : (List.finRange 19).all (fun i => decide
   (138∈UpperZero11.locks i → 139∈UpperZero11.region i → 137∉UpperZero11.locks i →
    i.val=9 ∨ i.val=16 ∨ i.val=17))=true := by decide +kernel
 have index := of_decide_eq_true (List.all_eq_true.mp possible i (by simp)) member138 hero139 noLock137
 have parts := HeroLedger.Logged.end_append_perm cut.before.logged (by decide) [137] PairFirstCut11.originalGroup (by decide) (by decide)
 have markerPerm : (endGroup UpperFirstCut11.originalGroup cut.beforeOutcomes).Perm
     (endGroup [137] cut.beforeOutcomes++[138,191]) :=
   parts.trans ((List.Perm.refl _).append pairPerm)
 have headEq := GhostProjection.matches_unique cut.middle cut.actor cut.headOutcome (.push 138 (.stay 137)) cut.headEffect effect
 rw [headEq]
 have afterHero : cut.actor.state.player=138 := by rw [effect.2]
 rcases index with index|index|index
 · have exactIndex : i=⟨9,by decide⟩ := Fin.ext index
   subst i
   have markerMember : 216∈endGroup [137] cut.beforeOutcomes := by
     have selectedMarker : 216∈endGroup UpperFirstCut11.originalGroup cut.beforeOutcomes := upperPerm.mem_iff.mpr (by decide)
     simpa using markerPerm.mem_iff.mp selectedMarker
   have markerTag := Upper190Identity11.singleton_member _ 216 (Nat.le_trans (endGroup_length_le [137] cut.beforeOutcomes) (by simp)) markerMember
   have afterPerm := update_perm upperPerm (.push 138 (.stay 137))
   have concrete : (update (UpperZero11.locks ⟨9,by decide⟩) (.push 138 (.stay 137))).Perm
       (WestRank11.locks ⟨10,by decide⟩) := by decide +kernel
   have linked := afterPerm.trans concrete
   refine ⟨⟨10,by decide⟩,?_,?_,?_,?_,still191⟩
   · rw [afterHero]; decide +kernel
   · exact fun _ found => linked.mem_iff.mpr found
   · rw [markerTag]; decide +kernel
   · decide +kernel
 · have exactIndex : i=⟨16,by decide⟩ := Fin.ext index
   subst i
   have markerMember : 164∈endGroup [137] cut.beforeOutcomes := by
     have selectedMarker : 164∈endGroup UpperFirstCut11.originalGroup cut.beforeOutcomes := upperPerm.mem_iff.mpr (by decide)
     simpa using markerPerm.mem_iff.mp selectedMarker
   have markerTag := Upper190Identity11.singleton_member _ 164 (Nat.le_trans (endGroup_length_le [137] cut.beforeOutcomes) (by simp)) markerMember
   have afterPerm := update_perm upperPerm (.push 138 (.stay 137))
   have concrete : (update (UpperZero11.locks ⟨16,by decide⟩) (.push 138 (.stay 137))).Perm
       (WestRank11.locks ⟨1,by decide⟩) := by decide +kernel
   have linked := afterPerm.trans concrete
   refine ⟨⟨1,by decide⟩,?_,?_,?_,?_,still191⟩
   · rw [afterHero]; decide +kernel
   · exact fun _ found => linked.mem_iff.mpr found
   · rw [markerTag]; decide +kernel
   · decide +kernel
 · have exactIndex : i=⟨17,by decide⟩ := Fin.ext index
   subst i
   have markerMember : 190∈endGroup [137] cut.beforeOutcomes := by
     have selectedMarker : 190∈endGroup UpperFirstCut11.originalGroup cut.beforeOutcomes := upperPerm.mem_iff.mpr (by decide)
     simpa using markerPerm.mem_iff.mp selectedMarker
   have markerTag := Upper190Identity11.singleton_member _ 190 (Nat.le_trans (endGroup_length_le [137] cut.beforeOutcomes) (by simp)) markerMember
   have afterPerm := update_perm upperPerm (.push 138 (.stay 137))
   have concrete : (update (UpperZero11.locks ⟨17,by decide⟩) (.push 138 (.stay 137))).Perm
       (WestRank11.locks ⟨5,by decide⟩) := by decide +kernel
   have linked := afterPerm.trans concrete
   refine ⟨⟨5,by decide⟩,?_,?_,?_,?_,still191⟩
   · rw [afterHero]; decide +kernel
   · exact fun _ found => linked.mem_iff.mpr found
   · rw [markerTag]; decide +kernel
   · decide +kernel

#print axioms after138west
end Owner1007.WestRankInitial11
