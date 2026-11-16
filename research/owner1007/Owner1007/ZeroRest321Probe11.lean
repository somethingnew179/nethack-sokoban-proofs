import Owner1007.UpperCutBudget11
namespace Owner1007.ZeroRest321Probe11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A prescribed original canonical prefix, not a completing trace. -/
def path : List Dir := [.east,.east,.east,.east,.southEast,.southEast,.south,.southEast,.south,.southWest,.southWest,.southWest,.south,.southEast,.southEast,.east,.northEast,.southEast,.west]
def result : State := {player:=321,boulders:=320::soko1_1.initial.boulders.erase 321,holes:=soko1_1.initial.holes}
theorem checked : run soko1_1.board soko1_1.initial path=some ⟨result,1,19⟩ := by decide +kernel
theorem trace : Trace soko1_1.board soko1_1.initial path result 1 19 := run_sound _ _ _ _ checked
def other : List Cell := soko1_1.initial.boulders.filter fun c => !UpperBudget11.Rest.contains c
/-- Zero energy of the whole Rest prefix does not imply stationary original321.
The sole push moves321 west to320; the full18-token energy is also zero. -/
theorem zero_energy_moved321 : ∃ outcomes,
 Logged soko1_1.board soko1_1.initial path result 1 19 outcomes ∧
 energy soko1_1.initial result UpperBudget11.Rest outcomes=0 ∧
 (321:Cell)∉result.boulders ∧ (320:Cell)∈result.boulders := by
 obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
 have total := HeroLedger.Logged.total_energy logged weightAt NetHack.Soko11Hero315.holeWeight
 change energy soko1_1.initial result soko1_1.initial.boulders outcomes =
   (1:Int)+weightSum (weightAt result) result.boulders+weightSum NetHack.Soko11Hero315.holeWeight result.holes-
   (weightSum (weightAt soko1_1.initial) soko1_1.initial.boulders+
    weightSum NetHack.Soko11Hero315.holeWeight soko1_1.initial.holes) at total
 have start : weightSum (weightAt soko1_1.initial) soko1_1.initial.boulders+
   weightSum NetHack.Soko11Hero315.holeWeight soko1_1.initial.holes=315 := by decide +kernel
 have finish : weightSum (weightAt result) result.boulders+
   weightSum NetHack.Soko11Hero315.holeWeight result.holes=314 := by decide +kernel
 have allZero : energy soko1_1.initial result soko1_1.initial.boulders outcomes=0 := by omega
 have perm : soko1_1.initial.boulders.Perm (UpperBudget11.Rest++other) := by decide +kernel
 have same := Hero315Frame11.energy_perm perm soko1_1.initial result outcomes
 have split := Hero315Frame11.energy_split logged UpperBudget11.Rest other (by decide +kernel) (by decide +kernel)
 have nnRest := Hero315Frame11.energy_nonnegative logged UpperBudget11.Rest (by decide +kernel) (by decide +kernel)
 have nnOther := Hero315Frame11.energy_nonnegative logged other (by decide +kernel) (by decide +kernel)
 exact ⟨outcomes,logged,by omega,by decide +kernel,by decide +kernel⟩
#print axioms trace
#print axioms zero_energy_moved321
end Owner1007.ZeroRest321Probe11
