import NetHack.SokobanLinearPhases.Map11.Check00
import NetHack.SokobanLinearPhases.Map11.Check01
import NetHack.SokobanLinearPhases.Map11.Check02
import NetHack.SokobanLinearPhases.Map11.Check03
import NetHack.SokobanLinearPhases.Map11.Check04
import NetHack.SokobanLinearPhases.Map11.Check05
import NetHack.SokobanLinearPhases.Map11.Check06
import NetHack.SokobanLinearPhases.Map11.Check07
import NetHack.SokobanLinearPhases.Map11.Check08
import NetHack.SokobanLinearPhases.Map11.Check09
import NetHack.SokobanLinearPhases.Map11.Check10
import NetHack.SokobanLinearPhases.Map11.Check11
import NetHack.SokobanLinearPhases.Map11.Check12
import NetHack.SokobanLinearPhases.Map11.Check13
import NetHack.SokobanLinearPhases.Map11.Check14
import NetHack.SokobanLinearPhases.Map11.Check15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.SokobanLinearPhases.Map11
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
theorem all_walks (phase : Nat) (active : phase < soko1_1.initial.holes.length) : walkCheck soko1_1.board soko1_1.initial.holes heroes phase = true := by
  have bound : phase < 16 := active
  have choices : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 ∨ phase = 5 ∨ phase = 6 ∨ phase = 7 ∨ phase = 8 ∨ phase = 9 ∨ phase = 10 ∨ phase = 11 ∨ phase = 12 ∨ phase = 13 ∨ phase = 14 ∨ phase = 15 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact walks00
  · exact walks01
  · exact walks02
  · exact walks03
  · exact walks04
  · exact walks05
  · exact walks06
  · exact walks07
  · exact walks08
  · exact walks09
  · exact walks10
  · exact walks11
  · exact walks12
  · exact walks13
  · exact walks14
  · exact walks15
theorem all_pushes (phase : Nat) (active : phase < soko1_1.initial.holes.length) : pushCheck soko1_1.board soko1_1.initial.holes heroes crates phase = true := by
  have bound : phase < 16 := active
  have choices : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 ∨ phase = 5 ∨ phase = 6 ∨ phase = 7 ∨ phase = 8 ∨ phase = 9 ∨ phase = 10 ∨ phase = 11 ∨ phase = 12 ∨ phase = 13 ∨ phase = 14 ∨ phase = 15 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pushes00
  · exact pushes01
  · exact pushes02
  · exact pushes03
  · exact pushes04
  · exact pushes05
  · exact pushes06
  · exact pushes07
  · exact pushes08
  · exact pushes09
  · exact pushes10
  · exact pushes11
  · exact pushes12
  · exact pushes13
  · exact pushes14
  · exact pushes15
def certificate : Certificate soko1_1.board soko1_1.initial.holes :=
  ofChecks _ _ heroes crates all_walks all_pushes
theorem initial_good : Good certificate soko1_1.initial := by
  refine ⟨by decide +kernel, 0, by decide +kernel, rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
theorem trace_phase_invariant {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_1.board soko1_1.initial directions final pushes moves) :
    Good certificate final := trace_good certificate trace initial_good
theorem trace_hole_order {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_1.board soko1_1.initial directions final pushes moves) :
    ∃ phase ≤ 16, final.holes = soko1_1.initial.holes.drop phase ∧ final.player ∈ heroes phase ∧ final.boulders ⊆ crates phase := by
  exact (trace_phase_invariant trace).2
end NetHack.SokobanLinearPhases.Map11
