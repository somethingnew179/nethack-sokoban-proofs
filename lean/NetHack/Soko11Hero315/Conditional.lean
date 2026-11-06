import NetHack.Soko11Hero315.Initial
namespace NetHack.Soko11Hero315
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
def WalkRows : Prop := ∀ phase, phase < soko1_1.initial.holes.length → ∀ box ∈ phases.crates phase,
  walkRow soko1_1.board (soko1_1.initial.holes.drop phase) (phases.heroes phase) box (fun hero => weight phase hero box) = true
def PushRows : Prop := ∀ phase, phase < soko1_1.initial.holes.length → ∀ box ∈ phases.crates phase,
  pushRow soko1_1.board (soko1_1.initial.holes.drop phase) (phases.heroes phase) box
    (fun hero => weight phase hero box) (fun landing => weight phase box landing) holeWeight = true
def AdvanceRows : Prop := ∀ phase, phase < soko1_1.initial.holes.length → ∀ box ∈ phases.crates phase,
  advanceRow soko1_1.board (soko1_1.initial.holes.drop phase) box
    (fun hero => weight phase hero box) (fun hero => weight (phase+1) hero box) = true
def certificate (walked : WalkRows) (pushed : PushRows) (advanced : AdvanceRows) :
    HeroPhasePotential.Certificate soko1_1.board soko1_1.initial.holes phases :=
  ofRows soko1_1.board soko1_1.initial.holes phases weight holeWeight reverse_checked
    disjoint_checked walked pushed advanced (fun hero box => by
      change weight horizon hero box ≤ 0
      rw [terminal]
      exact Int.le_refl 0)
theorem certificate_value (walked : WalkRows) (pushed : PushRows) (advanced : AdvanceRows) (s : State) :
    HeroPhasePotential.value (certificate walked pushed advanced) s = candidateValue s := rfl
theorem lower_bound_if_all_scalar_rows (walked : WalkRows) (pushed : PushRows) (advanced : AdvanceRows)
    {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_1.board soko1_1.initial directions final pushes moves) (completed : Goal final) :
    315 ≤ pushes := by
  apply HeroPhasePotential.pushes_lower_bound (certificate walked pushed advanced)
    NetHack.SokobanLinearPhases.Map11.initial_good 315 ?_ trace completed
  rw [certificate_value]
  exact proposed_initial_value
end NetHack.Soko11Hero315
