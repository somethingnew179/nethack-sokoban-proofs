import Owner1007.AfterJ12Data
namespace Owner1007.AfterJ12
open NetHack.Sokoban
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem ringMatrix : ∀ kind, PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes (ringLocks kind) (ringRegion kind) (ringPaid kind) = true := by decide +kernel
#print axioms ringMatrix
end Owner1007.AfterJ12
