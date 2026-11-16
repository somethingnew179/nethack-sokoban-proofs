import Owner1007.NorthEvents12
import Owner1007.Lower291Trade12
import Owner1007.CageLedger12
namespace Owner1007.After265ZeroCore12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem impossible {state t final dirs pushes moves outcomes history past pastMoves}
 (head : step soko1_2.board state .south=some t)
 (effect : Matches state t (.push 265 (.stay 291)))
 (logged : Logged soko1_2.board t.state dirs final pushes moves outcomes)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final)
 (group : List Cell) (gUnique : group.Nodup) (gActual : group⊆t.state.boulders) (owner : (291:Cell)∈group)
 (j : Fin 5) (bottomBefore : ([318,NorthEvents12.current j]:List Cell)⊆state.boulders)
 (coreZero : energy p group outcomes≤0)
 (bottomCheap : energy p [318,NorthEvents12.current j] outcomes≤2) :False := by
 obtain ⟨result,_,pushed⟩ := effect_push_data head effect
 obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear soko1_2.board state 265 .south result pushed).2
 have same : dest=291 := Option.some.inj (next.symm.trans (by decide +kernel : advance soko1_2.board 265 .south=some 291))
 subst dest
 have away : NorthEvents12.current j≠291 := by
   intro bad
   exact clear (bottomBefore (by rw [bad];simp))
 have small : j.val<4 := by
   have check : ∀ j,NorthEvents12.current j≠291→j.val<4 := by decide +kernel
   exact check j away
 let i : Fin 4 := ⟨j.val,small⟩
 have currentEq : After26512.current i=NorthEvents12.current j := by
   have check : ∀ (i:Fin 4) (j:Fin 5),i.val=j.val→After26512.current i=NorthEvents12.current j := by decide +kernel
   exact check i j rfl
 have bUnique : ([318,NorthEvents12.current j]:List Cell).Nodup := by
   have check : ∀ j,([318,NorthEvents12.current j]:List Cell).Nodup := by decide +kernel
   exact check j
 have no265 : (265:Cell)∉([318,NorthEvents12.current j]:List Cell) := by
   have check : ∀ j,(265:Cell)∉([318,NorthEvents12.current j]:List Cell) := by decide +kernel
   exact check j
 have kept := GhostSubset.update_subset state t (.push 265 (.stay 291)) effect
   [318,NorthEvents12.current j] bUnique bottomBefore
 have updateSame : update [318,NorthEvents12.current j] (.push 265 (.stay 291))=[318,NorthEvents12.current j] := by
   simp only [update,move,if_neg no265]
 rw [updateSame] at kept
 have inside : After26512.locks i⊆t.state.boulders := by
   intro c member
   change c∈([291,318,After26512.current i]:List Cell) at member
   rw [currentEq] at member
   rcases List.mem_cons.mp member with same|bottom
   ·exact gActual (same.symm ▸ owner)
   ·exact kept bottom
 have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
 have nextActual := nextReached.boulders_nodup (by decide +kernel)
 have hero : t.state.player∈After26512.region i := by
   rw [matches_hero state t (.push 265 (.stay 291)) effect]
   exact After26512.start_hero i
 have trade := Lower291Trade12.trade logged nextReached completed i hero inside
 change 2≤energy p [291] outcomes∨3≤energy p [318,After26512.current i] outcomes at trade
 rw [currentEq] at trade
 rcases trade with core|bottom
 ·have singleInside : ([291]:List Cell)⊆group := by simpa using owner
  have mono := logged.energy_mono Generated.soko1_2_potential_valid nextActual [291] group
    (by decide +kernel) gUnique (List.Subset.trans singleInside gActual) gActual singleInside
  change energy p [291] outcomes≤energy p group outcomes at mono
  omega
 ·omega
#print axioms impossible
end Owner1007.After265ZeroCore12
