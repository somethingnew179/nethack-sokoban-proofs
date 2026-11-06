import NetHack.Sokoban.HeroPhasePotential.DebtRows
import NetHack.SokobanLinearPhases.Map11.Invariant
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315
open NetHack.Sokoban
abbrev phases := NetHack.SokobanLinearPhases.Map11.certificate
def horizon : Nat := 16
def stride : Nat := 468
def bits : Nat := 6

end NetHack.Soko11Hero315
