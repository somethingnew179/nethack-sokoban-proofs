import Owner1007.AfterTwo236Trap12
import Owner1007.AfterTwoMixedTrap12
namespace Owner1007.AfterTwoOrdinaryTrap12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def C (kind : Fin 2) : List Cell :=
 if kind.val=0 then After21023612.ordinary else After23821012.ordinary
def B (i : Fin 5) : List Cell := [318,NorthEvents12.current i]
def K (kind : Fin 2) (i : Fin 5) : List Cell :=
 if kind.val=0 then After21023612.locks i else After23821012.locks i
def R (kind : Fin 2) (i : Fin 5) : List Cell :=
 if kind.val=0 then After21023612.region i else After23821012.region i
theorem impossible {state final dirs pushes moves outcomes history past pastMoves}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (kind : Fin 2) (i : Fin 5)
 (hero : state.player∈R kind i) (inside : K kind i⊆state.boulders)
 (coreCheap : energy p (C kind) outcomes≤2)
 (bottomCheap : energy p (B i) outcomes≤2) :False := by
 obtain ⟨k,h⟩ := kind
 have cases : k=0∨k=1 := by omega
 rcases cases with rfl|rfl
 ·exact AfterTwo236Trap12.impossible logged reached completed i hero inside coreCheap bottomCheap
 ·exact AfterTwoMixedTrap12.impossible logged reached completed i hero inside coreCheap bottomCheap
#print axioms impossible
end Owner1007.AfterTwoOrdinaryTrap12
