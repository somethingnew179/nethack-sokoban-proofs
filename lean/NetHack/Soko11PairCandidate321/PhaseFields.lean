import NetHack.Soko11PairCandidate321.Conditional
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban NetHack.Sokoban.HazardPattern

def PositiveActionsAt (phase : Nat) : Prop :=
  ∀ hero ∈ NetHack.Soko11Hero315.phases.heroes phase,
    ∀ group, group.Nodup → group ⊆ NetHack.Soko11Hero315.phases.crates phase → group.length ≤ 2 →
    hero ∈ soko1_1.board.floor → hero ∉ soko1_1.board.doors →
    hero ∉ soko1_1.initial.holes.drop phase → hero ∉ group → 0 < bonus phase hero group →
    ∀ direction outcome,
    stepOracle soko1_1.board (PatternCorrection.project group)
      (PatternCorrection.project (soko1_1.initial.holes.drop phase)) hero direction = some outcome →
    localBound phase hero group outcome

def PositiveEnvironmentsAt (phase : Nat) : Prop :=
  ∀ hero ∈ NetHack.Soko11Hero315.phases.heroes phase,
    ∀ group, group.Nodup → group ⊆ NetHack.Soko11Hero315.phases.crates phase →
    group ⊆ NetHack.Soko11Hero315.phases.crates (phase+1) → group.length ≤ 2 →
    hero ∈ soko1_1.board.floor → hero ∉ soko1_1.board.doors →
    hero ∉ soko1_1.initial.holes.drop phase → hero ∉ group → 0 < bonus phase hero group →
    valueAt phase hero group ≤ valueAt (phase+1) hero group

end NetHack.Soko11PairCandidate321
