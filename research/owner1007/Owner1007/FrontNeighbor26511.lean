import Owner1007.StationaryGuards11
namespace Owner1007.FrontNeighbor26511
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem guards (cell : Cell) (member : cell∈([264,266] : List Cell)) :
 (List.range 16).all (StationaryGuards11.guardCheck 265 [cell])=true := by
 rcases List.mem_cons.mp member with rfl|later
 ·decide +kernel
 ·have same : cell=266 := List.mem_singleton.mp later
  subst cell;decide +kernel

theorem tag {history state past pastMoves dirs final pushes moves outcomes}
 (cell : Cell) (member : cell∈([264,266] : List Cell))
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (front : 265∈state.boulders) (present : cell∈state.boulders)
 (stationary : ownPushes [265] outcomes=0) (cheap : energy state final [cell] outcomes<2) :
 endGroup [cell] outcomes=[cell] := by
 obtain ⟨dest,inside,result⟩ := StationaryGuards11.guard_logged (guards cell member) logged
   (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached) front present (by simp) stationary cheap
 have same : dest=cell := List.mem_singleton.mp inside
 simpa only [same] using result
#print axioms guards
#print axioms tag
end Owner1007.FrontNeighbor26511
