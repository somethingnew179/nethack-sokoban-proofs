import Owner1007.Arrival187Left21211
namespace Owner1007.Arrival187PairCapacity11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.Arrival187Left21211
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem future_two {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (inside : [187,212]⊆state.boulders) (hero : state.player∈region 0)
 (capacity : ¬([187,212] : List Cell)⊆final.boulders) :
 2≤energy state final [187,212] outcomes := by
 by_cases enough : 2≤energy state final [187,212] outcomes
 ·exact enough
 ·have cheap : energy state final [187,212] outcomes<2 := by omega
  have price : ∀ state dir t outcome group,
   HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
   group.Nodup →group⊆state.boulders →group.length≤2 →
   step soko1_1.board state dir=some t →Matches state t outcome →
   OwnedCorral11.PaidStep paid group dir t →
   2≤charge (groupCertificate 2).holeWeight group outcome+
     (groupCertificate 2).groupValue t.state (update group outcome)-(groupCertificate 2).groupValue state group:=by
   intro state dir t outcome group valid unique inside bounded head effect pays
   exact priced valid unique inside head effect pays
  have retained := OwnedCorralAny11.small_energy_good closed (by decide +kernel)
   (groupCertificate 2) 2 price logged (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached)
   [187,212] (by decide) inside (by decide) ⟨0,hero,fun _ h=>h⟩ reached.holes_sublist.subset cheap
  obtain ⟨i,_,locksInside⟩ := retained
  have same : i=0 := Fin.ext (by omega)
  rw [same] at locksInside
  have actual := (logged.end_subset (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached).1 [187,212] (by decide) inside).2
  exact False.elim (capacity (List.Subset.trans locksInside actual))
#print axioms future_two
end Owner1007.Arrival187PairCapacity11
