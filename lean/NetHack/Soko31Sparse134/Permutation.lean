import NetHack.Soko31Sparse134.Value
import NetHack.Sokoban.HeroPhasePotential.Residual
namespace NetHack.Soko31Sparse134
open NetHack.Sokoban NetHack.Sokoban.StatePermutation NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf)
theorem value_respects (a b : State) (related : Equivalent a b) : value a = value b := by
  have sameBase : base a = base b := HeroPhasePotential.Residual.value_respects cert a b related
  have samePhase : phaseOf soko3_1.initial.holes a = phaseOf soko3_1.initial.holes b := by
    simp only [phaseOf,related.holes.length_eq]
  have samePattern : project a.boulders = project b.boulders := funext fun _ => related.boulders.contains_eq
  simp only [value,sameBase,samePhase,related.player,samePattern]
end NetHack.Soko31Sparse134
