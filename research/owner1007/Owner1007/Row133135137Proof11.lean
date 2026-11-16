import Owner1007.Row13313513711
namespace Owner1007.Row13313513711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def G : List Cell := [133,135,137]
def anchor (i : Fin 7) : Cell := match i.val with |3=>132 |4=>133 |5=>134 |6=>135 |_=>0
theorem bad_member : ∀i,3≤i.val→anchor i∈locks i := by decide +kernel
theorem bad_check : ∀i,3≤i.val→Owner1007.lockedCheck soko1_1.board (locks i)=true := by decide +kernel

theorem no_first_west_with
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 137 (.stay 136)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (stationary : ownPushes [137] before=0)
 (gone : endGroup G (before++.push 137 (.stay 136)::after)=[]) : False := by
 have quiet := quiet_of_stationary first G stationary
 have initialGood : OwnedCorral11.Good locks region soko1_1.initial G := ⟨0,by decide +kernel,by decide⟩
 have retained := Upper216Eight11.quiet_good_any closed unique quiet (by decide) (by decide) (by decide) initialGood (by simp)
 obtain ⟨i,_,locksInside⟩ := retained
 have actual := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1
 have facts := first.end_subset (by decide) G (by decide) (by decide)
 let group := endGroup G before
 have remaining : endGroup group (.push 137 (.stay 136)::after)=[] := by
  rw [endGroup_append] at gone
  exact gone
 let tail := Logged.cons head effect last
 by_cases bad : 3≤i.val
 ·have frozen := Owner1007.locked_of_check _ _ (bad_check i bad)
  exact Upper216Eight11.frozen_absurd tail actual facts.1 facts.2 frozen
   (List.Subset.trans locksInside facts.2) (bad_member i bad) (locksInside (bad_member i bad)) remaining
 ·have choices : i.val=0∨i.val=1∨i.val=2 := by omega
  have free136 : 136∉state.boulders := by
   obtain ⟨result,_,push⟩ := effect_push_data head effect
   obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear _ _ _ _ _ push).2
   have same : dest=136 := Option.some.inj (next.symm.trans (show advance soko1_1.board 137 .west=some 136 by decide +kernel))
   exact same ▸ clear
  rcases choices with zero|one|two
  ·have iZero : i=0 := Fin.ext zero
   rw [iZero] at locksInside
   have own137 : 137∈group := locksInside (by decide)
   have own135 : 135∈group := locksInside (by decide)
   let oneLog : Logged soko1_1.board state [.west] t.state t.pushCost 1 [.push 137 (.stay 136)] := .cons head effect (.nil _)
   have nextFacts := oneLog.end_subset actual group facts.1 facts.2
   change (update group (.push 137 (.stay 136))).Nodup ∧ update group (.push 137 (.stay 136))⊆t.state.boulders at nextFacts
   have owns135 : 135∈update group (.push 137 (.stay 136)) := by
    simp only [update,move,if_pos own137,post]
    exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :135≠137)).mpr own135)
   have physical : ([135,136] : List Cell)⊆t.state.boulders := by
    intro c h
    rcases List.mem_cons.mp h with rfl|later
    ·exact nextFacts.2 owns135
    ·have same : c=136 := List.mem_singleton.mp later
     subst c
     rw [effect.2]
     exact List.mem_cons_self
   have afterGone : endGroup (update group (.push 137 (.stay 136))) after=[] := remaining
   exact Upper216Eight11.frozen_absurd last (step_boulders_nodup _ _ _ _ actual head)
    nextFacts.1 nextFacts.2 (Owner1007.locked_of_check _ [135,136] (by decide +kernel)) physical (by decide) owns135 afterGone
  ·have iOne : i=1 := Fin.ext one
   rw [iOne] at locksInside
   exact free136 (facts.2 (locksInside (by decide)))
  ·have iTwo : i=2 := Fin.ext two
   rw [iTwo] at locksInside
   exact free136 (facts.2 (locksInside (by decide)))
#print axioms no_first_west_with
end Owner1007.Row13313513711
