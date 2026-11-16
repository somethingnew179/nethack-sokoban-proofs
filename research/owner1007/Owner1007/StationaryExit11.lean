import Owner1007.StationaryGuards11
import Owner1007.HeroEnergyTrace11
namespace Owner1007.StationaryExit11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

theorem after_push_survives {board initial beforeDirs middle beforePushes beforeMoves before
    dir t afterDirs final afterPushes afterMoves after source park mate}
 (first : Logged board initial beforeDirs middle beforePushes beforeMoves before)
 (checked : step board middle dir=some t) (effect : Matches middle t (.push source (.stay park)))
 (last : Logged board t.state afterDirs final afterPushes afterMoves after)
 (actualUnique : initial.boulders.Nodup) (matePresent : mate∈initial.boulders)
 (different : mate≠source)
 (prior : endGroup [source] before=[source])
 (guarded : endGroup [mate] before=[mate] ∨ endGroup [mate] before=[park])
 (locked : Owner1007.Locked board [park,mate])
 (targets : advance board source dir=some park) :
 endGroup [source] (before ++ .push source (.stay park) :: after)≠[] := by
 have mateSubset : [mate]⊆initial.boulders := by simpa using matePresent
 have selected := first.end_subset actualUnique [mate] (by simp) mateSubset
 obtain ⟨result,_,push⟩ := effect_push_data checked effect
 have noPark : park∉middle.boulders := by
   obtain ⟨dest,next,_,_,empty⟩ := (push_first_clear _ _ _ _ _ push).2
   have eq : dest=park := Option.some.inj (next.symm.trans targets)
   simpa only [eq] using empty
 have mateMiddle : mate∈middle.boulders := by
   rcases guarded with normal | impossible
   · exact selected.2 (by rw [normal]; simp)
   · exact False.elim (noPark (selected.2 (by rw [impossible]; simp)))
 have nextShape : t.state.boulders=park::middle.boulders.erase source := by rw [effect.2]
 have pairInside : [park,mate]⊆t.state.boulders := by
   rw [nextShape]
   intro c found
   rcases List.mem_cons.mp found with rfl | rest
   · simp
   · have same : c=mate := List.mem_singleton.mp rest
     subst c
     exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne different).mpr mateMiddle)
 have survives := locked_identity last locked pairInside (show park∈[park,mate] by simp)
 rw [endGroup_append,prior]
 simpa only [endGroup,update,move,List.mem_cons,List.not_mem_nil,or_false,if_true,
   post,List.erase_cons_head,survives] using (show ([park] : List Cell)≠[] by simp)

theorem survives139 {beforeDirs middle beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_1.board middle .east=some t) (effect : Matches middle t (.push 139 (.stay 140)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (stationary : ownPushes [139] before=0)
 (cheap : energy soko1_1.initial middle [141] before<2) :
 endGroup [139] (before ++ .push 139 (.stay 140) :: after)≠[] :=
 after_push_survives first checked effect last (by decide +kernel) (by decide +kernel)
   (by decide) (no_push_unchanged _ _ stationary) (StationaryGuards11.guard141 first stationary cheap)
   (Owner1007.locked_of_check _ _ (by decide +kernel)) (by decide +kernel)

theorem survives191 {beforeDirs middle beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_1.board middle .east=some t) (effect : Matches middle t (.push 191 (.stay 192)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (stationary : ownPushes [191] before=0)
 (cheap : energy soko1_1.initial middle [193] before<2) :
 endGroup [191] (before ++ .push 191 (.stay 192) :: after)≠[] :=
 after_push_survives first checked effect last (by decide +kernel) (by decide +kernel)
   (by decide) (no_push_unchanged _ _ stationary) (StationaryGuards11.guard193 first stationary cheap)
   (Owner1007.locked_of_check _ _ (by decide +kernel)) (by decide +kernel)

#print axioms survives139
#print axioms survives191
end Owner1007.StationaryExit11
