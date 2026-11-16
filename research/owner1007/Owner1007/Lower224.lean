import Owner1007.North224Assembly12
import Owner1007.RingPrepared12
namespace Owner1007.Lower224
open NetHack.Sokoban

theorem ring_reserve : North224Assembly12.RingReserve := by
 intro state final dirs pushes moves outcomes history past pastMoves logged reached group unique subset completed i hero inside
 exact RingPrepared12.ring_energy_six logged reached group unique subset completed (i:=i) hero inside

/-- Universal bound for every original canonical full-map completing Trace. -/
theorem pushes_lower_bound {dirs final pushes moves}
 (trace : Trace soko1_2.board soko1_2.initial dirs final pushes moves) (completed : Goal final) :
 224≤pushes := North224Assembly12.canonical_bound ring_reserve trace completed
#print axioms ring_reserve
#print axioms pushes_lower_bound
end Owner1007.Lower224
