/- Facts derived from the existing original phase invariant. No added
premises on starting/completing Traces and no new puzzle profile. -/
import NetHack.Soko32Disjoint.Initial
import NetHack.SokobanLinearPhases.Map32.Invariant
namespace NetHack.Soko32Disjoint
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem phase_disjoint : ∀ phase : Fin 13,
    ∀ c ∈ NetHack.SokobanLinearPhases.Map32.crates phase,
      c ∉ soko3_2.initial.holes.drop phase := by decide +kernel

theorem trace_disjoint {history : List Dir} {state : State} {pushes moves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state pushes moves) :
    ∀ c ∈ state.boulders, c ∉ state.holes := by
  obtain ⟨phase,bound,holes,hero,inside⟩ := NetHack.SokobanLinearPhases.Map32.trace_hole_order reached
  intro c member
  rw [holes]
  exact phase_disjoint ⟨phase,by omega⟩ c (inside member)

end NetHack.Soko32Disjoint
