import Owner1007.LeftSix31711
import Owner1007.Fixed317Shaft11
import Owner1007.Tight32511
namespace Owner1007.LeftSix317Canonical11
open NetHack.Sokoban
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem pair_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (stationary : ownPushes [317] outcomes=0) :
 6≤energy soko1_1.initial final [186,212] outcomes :=
 LeftSix31711.pair_six Fixed317Shaft11.closed Fixed317Shaft11.unique Fixed317Shaft11.size
   logged completed stationary
/-- A hypothetical325-push completion must move original317.
This excludes one of the two possible unmoved zero-debt survivor branches. -/
theorem moves317_at325 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325) : ownPushes [317] outcomes≠0 := by
 intro stationary
 obtain ⟨_,_,left,_⟩ := Tight32511.budgets logged completed cheap
 change energy soko1_1.initial final [186,212] outcomes=4 at left
 have six := pair_six logged completed stationary
 omega
#print axioms pair_six
#print axioms moves317_at325
end Owner1007.LeftSix317Canonical11
