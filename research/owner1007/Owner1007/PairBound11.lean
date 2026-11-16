import Owner1007.OwnedCorralBound11
import Owner1007.PairStrict11
import Owner1007.PairPath11
import Owner1007.Hero315Frame11
namespace Owner1007.PairBound11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
theorem pair_energy {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) :
 2 ≤ Hero315Frame11.energy soko1_1.initial final [139,191] outcomes := by
 have priced : ∀ state dir t outcome group,
   HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
   group.Nodup → group ⊆ state.boulders → group.length ≤ 2 →
   step soko1_1.board state dir = some t → Matches state t outcome →
   OwnedCorral11.PaidStep PairPath11.paid group dir t →
   2 ≤ charge (Hero315Frame11.groupCertificate 2).holeWeight group outcome +
    (Hero315Frame11.groupCertificate 2).groupValue t.state (update group outcome) -
    (Hero315Frame11.groupCertificate 2).groupValue state group := by
  intro state dir t outcome group good unique inside bounded checked effect pays
  exact PairStrict11.exit_row Hero315Frame11.scalar rfl good checked effect unique inside pays
 have initialGood : OwnedCorral11.Good PairPath11.locks PairPath11.region soko1_1.initial [139,191] := by
  refine ⟨⟨0,by decide⟩,?_,?_⟩ <;> decide +kernel
 have debt : (Hero315Frame11.groupCertificate 2).groupValue soko1_1.initial [139,191] ≤ -(2:Int) := by decide +kernel
 exact OwnedCorral11.energy_bound PairPath11.closed PairPath11.unique PairPath11.size
  (Hero315Frame11.groupCertificate 2) 2 priced logged NetHack.SokobanLinearPhases.Map11.initial_good
  [139,191] (by decide) (by decide) rfl initialGood (by simp) debt
  (Hero315Frame11.goal_value_zero completed _)
#print axioms pair_energy
end Owner1007.PairBound11
