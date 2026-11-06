import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban.DecisionDAGCountedBounded
import NetHack.Sokoban.PackedMasks
import NetHack.Sokoban.PackedRestrictionChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified
open NetHack.Sokoban
def cells : List Cell := Shared.cells
abbrev read := Shared.read
abbrev bounds := Shared.bounds
def label := Shared.label
def updateCount : Nat := 379104
def restrictionCount : Nat := 1345235
def numericCount : Nat := 78320
end NetHack.Soko12Forward220.Unified
