import Owner1007.PreCageFacts12
namespace Owner1007.NorthBlockedHeads12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem south210 : ∀ i : Fin 10, ∀ hero∈PreCage12.northRegion i,
 advance soko1_2.board hero .south=some 210 →
 BlockedPush soko1_2.board (PreCage12.northLocks i) 210 .south := by decide +kernel
theorem south238 : ∀ i : Fin 10, ∀ hero∈PreCage12.northRegion i,
 advance soko1_2.board hero .south=some 238 →
 BlockedPush soko1_2.board (PreCage12.northLocks i) 238 .south := by decide +kernel
#print axioms south210
#print axioms south238
end Owner1007.NorthBlockedHeads12

