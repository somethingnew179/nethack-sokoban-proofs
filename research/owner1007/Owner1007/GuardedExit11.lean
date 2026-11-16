import Owner1007.StationaryGuards11
import Owner1007.StationaryExit11
namespace Owner1007.GuardedExit11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

theorem survives {initial middle final : State} {source park mate box : Cell}
 {beforeDirs afterDirs : List Dir} {beforePushes beforeMoves afterPushes afterMoves : Nat}
 {before after : List Outcome} {dir : Dir} {t : Transition}
 (matrix : (List.range 16).all (StationaryGuards11.guardCheck source [mate,park])=true)
 (locked : Owner1007.Locked soko1_1.board [park,mate]) (different : mate≠source)
 (target : advance soko1_1.board source dir=some park)
 (first : Logged soko1_1.board initial beforeDirs middle beforePushes beforeMoves before)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate initial)
 (sourcePresent : source∈initial.boulders) (boxPresent : box∈initial.boulders)
 (boxMember : box∈([mate,park] : List Cell))
 (stationary : ownPushes [source] before=0) (cheap : energy initial middle [box] before<2)
 (checked : step soko1_1.board middle dir=some t)
 (effect : Matches middle t (.push source (.stay park)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) :
 endGroup [source] (before++ .push source (.stay park)::after)≠[] := by
 obtain ⟨next,member,tag⟩ := StationaryGuards11.guard_logged matrix first valid
   sourcePresent boxPresent boxMember stationary cheap
 have actualMate := first.end_subset valid.1 [box] (by simp) (by simpa using boxPresent)
 obtain ⟨result,_,push⟩ := effect_push_data checked effect
 obtain ⟨dest,adjacent,_,_,empty⟩ := (push_first_clear soko1_1.board middle source dir result push).2
 have same : dest=park := Option.some.inj (adjacent.symm.trans target)
 have clear : park∉middle.boulders := same ▸ empty
 have mateBefore : mate∈middle.boulders := by
   rcases List.mem_cons.mp member with normal|shifted
   · exact actualMate.2 (by rw [tag,normal]; simp)
   · have nextPark : next=park := List.mem_singleton.mp shifted
     exact False.elim (clear (actualMate.2 (by rw [tag,nextPark]; simp)))
 have pairInside : [park,mate]⊆t.state.boulders := by
   rw [effect.2]
   intro cell found
   rcases List.mem_cons.mp found with rfl|later
   · simp
   · have same : cell=mate := List.mem_singleton.mp later
     subst cell
     exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne different).mpr mateBefore)
 have fixed := locked_identity last locked pairInside (show park∈[park,mate] by simp)
 rw [endGroup_append,no_push_unchanged _ _ stationary]
 change endGroup (update [source] (.push source (.stay park))) after≠[]
 have updated : update [source] (.push source (.stay park))=[park] := by simp [update,move,post]
 rw [updated]
 rw [fixed]
 simp
#print axioms survives
end Owner1007.GuardedExit11
