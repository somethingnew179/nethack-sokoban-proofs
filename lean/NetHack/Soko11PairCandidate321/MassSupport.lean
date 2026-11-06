import NetHack.Soko11PairCandidate321.MassConditional
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mass_dominates (phase hero : Nat) (group : List Cell) (bound : phase ≤ 16) :
    LowerBounds.weightSum (NetHack.Soko11Hero315.weight phase hero) group ≤ massBasis.valueAt phase hero group :=
  GhostLastFillOracle.dominates scalar scalar_nonpositive phase hero group bound

theorem excess_implies_positive (phase hero : Nat) (group : List Cell) (bound : phase ≤ 16)
    (greater : massBasis.valueAt phase hero group < valueAt phase hero group) : 0 < bonus phase hero group := by
  have baseline := mass_dominates phase hero group bound
  unfold valueAt at greater
  simp only [Int.ofNat_eq_natCast] at greater
  omega

theorem excess_implies_pair (phase hero : Nat) (group : List Cell) (bound : phase ≤ 16)
    (greater : massBasis.valueAt phase hero group < valueAt phase hero group) : group.length = 2 := by
  have positive := excess_implies_positive phase hero group bound greater
  by_cases pair : group.length = 2
  · exact pair
  · simp only [bonus,if_neg pair] at positive
    omega

end NetHack.Soko11PairCandidate321
