import Owner1007.LeftFourLane11
import Owner1007.LeftFourLaneLift11
import Owner1007.LeftFourLaneLabels11
import Owner1007.Row190191Rest11
namespace Owner1007.RestBeforeRightRest11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem upper188_at189 {beforeDirs state beforePushes beforeMoves before t dirs final pushes moves outcomes}
 (past : UpperQuiet11.Quiet RightEarlyWords11.paid soko1_1.initial RightEarlyWords11.G beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .north=some t) (effect : Matches state t (.push 213 (.stay 187)))
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes) (completed : Goal final)
 (left : energy soko1_1.initial final [186] (before++.push 213 (.stay 187)::outcomes)≤4)
 (upper : energy soko1_1.initial final UpperBudget11.U6 (before++.push 213 (.stay 187)::outcomes)<8)
 (rest : energy soko1_1.initial final UpperBudget11.Rest (before++.push 213 (.stay 187)::outcomes)<2) :
 endGroup [188] before=[189] := by
 let suffix:=Logged.cons head effect last
 obtain ⟨i,tagLeft,tagRight,hero⟩:=LeftFourLaneLift11.prefix_word LeftFourLane11.closed LeftFourLane11.refined past suffix completed left upper rest
 have leftFacts:=past.logged.end_subset (by decide) [186] (by decide) (by decide)
 have rightFacts:=past.logged.end_subset (by decide) [188] (by decide) (by decide)
 have rightPresent : LeftFourLane11.right i∈state.boulders:=rightFacts.2 (by rw [tagRight];simp)
 have leftPresent : LeftFourLane11.left i∈state.boulders:=leftFacts.2 (by rw [tagLeft];simp)
 have shape : ∀i:Fin 21,LeftFourLane11.right i∈([185,186,187,188,189,190]:List Cell) := by decide +kernel
 have cases:=shape i
 simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
 have metadata : t.pushSource=some 213:=by rw [effect.2]
 have hero239 : state.player=239:=ActorPrices11.support_of_check 213 state.player .north 239 (by decide +kernel)
   (step_player_clear _ _ _ _ head).1 (PairPost11.source_adjacent head metadata)
 let one : Logged soko1_1.board state [.north] t.state t.pushCost 1 [.push 213 (.stay 187)] := .cons head effect (.nil _)
 have afterPair (cell : Cell) (member : cell∈([186,188]:List Cell)) (present : cell∈state.boulders) :
   [cell,187]⊆t.state.boulders := by
  have different : cell≠213:=by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl <;>decide
  rw [effect.2]
  intro c found
  rcases List.mem_cons.mp found with rfl|later
  ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne different).mpr present)
  ·have same : c=187:=List.mem_singleton.mp later
   subst c;exact List.mem_cons_self
 rcases cases with at185|at186|at187|at188|at189|at190
 ·have left184 : LeftFourLane11.left i=184:=by
   have row:∀i:Fin 21,LeftFourLane11.right i=185→LeftFourLane11.left i=184:=by decide +kernel
   exact row i at185
  have physical : [184,185]⊆state.boulders:=by
   intro c member
   rcases List.mem_cons.mp member with rfl|later
   ·simpa only [left184] using leftPresent
   ·have same : c=185:=List.mem_singleton.mp later
    subst c;simpa only [at185] using rightPresent
  exact False.elim (Spare315Rest11.frozen_pair past.logged suffix completed rest [184,185]
    (locked_of_check _ [184,185] (by decide +kernel)) (by decide) rfl physical (by decide))
 ·have physical:=afterPair 186 (by decide) (by simpa only [at186] using rightPresent)
  exact False.elim (Spare315Rest11.frozen_pair (past.logged.append one) last completed (by simpa only [List.append_assoc,List.singleton_append] using rest) [186,187]
    (locked_of_check _ [186,187] (by decide +kernel)) (by decide) rfl physical (by decide))
 ·have occupied : 187∈state.boulders:=by simpa only [at187] using rightPresent
  obtain ⟨result,_,push⟩:=effect_push_data head effect
  obtain ⟨dest,next,_,_,clear⟩:=(push_first_clear _ _ _ _ _ push).2
  have same : dest=187:=Option.some.inj (next.symm.trans (show advance soko1_1.board 213 .north=some 187 by decide +kernel))
  exact False.elim (clear (same.symm ▸ occupied))
 ·have physical:=afterPair 188 (by decide) (by simpa only [at188] using rightPresent)
  have reordered : [187,188]⊆t.state.boulders:=List.Subset.trans (by decide) physical
  exact False.elim (Spare315Rest11.frozen_pair (past.logged.append one) last completed (by simpa only [List.append_assoc,List.singleton_append] using rest) [187,188]
    (locked_of_check _ [187,188] (by decide +kernel)) (by decide) rfl reordered (by decide))
 ·simpa only [at189] using tagRight
 ·obtain ⟨j,_,_,tag191,_,fixed137,fixed139⟩:=RightEarlyWords11.quiet_packet past
  have qcases : RightEarlyWords11.q j=191∨RightEarlyWords11.q j=190:=by
   unfold RightEarlyWords11.q
   split <;>simp
  rcases qcases with q191|q190
  ·have current191 : 191∈state.boulders:=
    (past.logged.end_subset (by decide) [191] (by decide) (by decide)).2 (by rw [tag191,q191];simp)
   have physical : [190,191]⊆state.boulders:=by
    intro c member
    rcases List.mem_cons.mp member with rfl|later
    ·simpa only [at190] using rightPresent
    ·have same : c=191:=List.mem_singleton.mp later
     subst c;exact current191
   have heroRight : state.player∈Row19019111.region 0:=by rw [hero239];decide +kernel
   exact False.elim (Row190191Rest11.excluded past.logged suffix completed (by omega) rest
     fixed137 fixed139 physical heroRight)
  ·have both:=past.logged.end_subset (by decide) [188,191] (by decide) (by decide)
   have split:=HeroLedger.Logged.end_append_perm past.logged (by decide) [188] [191] (by decide) (by decide)
   rw [tagRight,at190,tag191,q190] at split
   have bad:=split.nodup_iff.mp both.1
   simpa using bad

#print axioms upper188_at189
end Owner1007.RestBeforeRightRest11
