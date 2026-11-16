import Owner1007.EastTight22912
import Owner1007.Upper187StartForcedSouth12
namespace Owner1007.East187BeforeS22912
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting Owner1007.OwnedEvents12
abbrev p := Generated.soko1_2Potential
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Before original213 first moves, original187 cannot move in a trace whose
whole Upper energy is at most2. North would require4; South collides with213. -/
theorem stationary_before_S {beforeDirs state beforePushes beforeMoves before
    afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_2.board EastPrice225.afterE beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_2.board state afterDirs final afterPushes afterMoves after)
 (stationaryS : ownPushes [213] before=0)
 (small : energy p Final222.U (before++after)≤2) : ownPushes [187] before=0 := by
 by_cases quiet : ownPushes [187] before=0
 ·exact quiet
 ·have moved : 0<ownPushes [187] before := Nat.pos_of_ne_zero quiet
  obtain ⟨bd,bp,bm,b1,middle,dir,t,source,ending,a1,ad,ap,am,shape,lead,head,effect,tail,stationary,member⟩ :=
    FirstOwnedPush.first_push first [187] moved
  have same : source=187 := List.mem_singleton.mp member
  subst source
  have reached := East22612.east_reached.append lead.trace
  have standing := step_player_clear soko1_2.board middle dir t head
  have present : (187:Cell)∈middle.boulders := by cases ending <;> exact effect.1
  obtain ⟨result,adjacent,pushed⟩ := effect_push_data head effect
  rcases Upper187StartForcedSouth12.direction_cases middle.player standing.1 dir
      (Geometry.all_directions dir) adjacent with blocked|north|south
  ·exact False.elim (CageFour12.blocked_impossible (by simpa using present) head effect blocked)
  ·subst dir
   have sameEnding := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel) (by decide +kernel) head effect
   subst ending
   have lower := Upper187Start12.first_north_four East22612.east_reached
     (by decide +kernel) (by decide +kernel) lead head effect (tail.append last) stationary
   change 4≤energy p Final222.U (b1++.push 187 (.stay 161)::(a1++after)) at lower
   have allShape : before++after=b1++.push 187 (.stay 161)::(a1++after) := by
     rw [shape]
     simp only [List.append_assoc,List.cons_append]
   rw [←allShape] at lower
   omega
  ·subst dir
   have zeroS : ownPushes [213] b1=0 := by
     rw [shape,Hero315Frame11.ownPushes_append] at stationaryS
     omega
   have tagS := no_push_unchanged [213] b1 zeroS
   have physicalS := lead.end_subset (by decide +kernel) [213] (by simp) (by decide +kernel)
   have presentS : (213:Cell)∈middle.boulders := physicalS.2 (by rw [tagS];simp)
   obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear soko1_2.board middle 187 .south result pushed).2
   have destEq : dest=213 := Option.some.inj (next.symm.trans (by decide +kernel))
   exact False.elim (clear (destEq.symm ▸ presentS))
#print axioms stationary_before_S
end Owner1007.East187BeforeS22912
