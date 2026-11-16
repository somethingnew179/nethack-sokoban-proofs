import Owner1007.FastCorral11
import Owner1007.PairPath11
namespace Owner1007.Pair13711
open NetHack.Sokoban
def patterns : List (List Cell) := [[137,191],[138,191],[164,191],[190,191],[216,191],
 [137,190],[137,164],[137,138],[137,112],[137,111]]
def locks (i : Fin 10) : List Cell := patterns[i.val]?.getD []
def H : List Cell := NetHack.SokobanLinearPhases.Map11.heroesRegion16
def B : List Cell := ZeroWord11.lowerTwo
def without (cells blocked : List Cell) : List Cell := cells.filter fun c => !blocked.contains c
def region (i : Fin 10) : List Cell :=
 match i.val with
 | 0 => without H [137,191]
 | 1 => PairPath11.region ⟨1,by decide⟩
 | 2 => PairPath11.region ⟨2,by decide⟩
 | 3 => PairPath11.region ⟨3,by decide⟩
 | 4 => PairPath11.region ⟨4,by decide⟩
 | 5 => without B [190]
 | 6 => B
 | 7 => B++[164]
 | 8 => B++[164,138,139,140,141,142,113,114,115,116]
 | _ => B++[164,138,139,140,141,142,113,114,115,116,112]
def paid (source : Cell) (dir : Dir) : Prop :=
 PairPath11.paid source dir ∨ (source=137 ∧ dir=.west) ∨ (source=111 ∧ dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by
 unfold paid
 infer_instance
end Owner1007.Pair13711

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Owner1007.Pair13711
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem size : ∀ i, (locks i).length=2 := by decide +kernel
#check unique
end Owner1007.Pair13711
