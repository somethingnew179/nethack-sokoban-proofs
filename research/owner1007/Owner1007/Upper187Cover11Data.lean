import Owner1007.UpperLocalPrice11
import Owner1007.FastCorral11
import Owner1007.UpperZero11
import Owner1007.PairPath11
namespace Owner1007.Upper187Cover11
open NetHack.Sokoban
def patterns : List (List Cell) := [[137,139,187,189],[138,139,187,189],[137,138,187,189],[139,164,187,189],[137,164,187,189],[139,187,189,190],[137,187,189,190],[138,187,189,190],[137,139,187,190],[137,139,188,190],[137,139,189,190],[137,139,164,187],[137,139,164,188],[137,139,164,189],[137,139,164,190],[137,139,164,191],[137,139,138,187],[137,139,138,188],[137,139,138,189],[137,139,138,190],[137,139,138,191],[137,139,138,164],[137,139,112,187],[137,139,112,188],[137,139,112,189],[137,139,112,190],[137,139,112,191],[137,139,112,164],[137,139,112,138],[187,189,216],[187,189,215],[187,189,214],[138,164],[164,190],[188,189],[187,213]]
def locks (i : Fin 36) : List Cell := patterns[i.val]?.getD []
def H : List Cell := NetHack.SokobanLinearPhases.Map11.heroesRegion16
def B : List Cell := ZeroWord11.lowerTwo
def without (cells blocked : List Cell) : List Cell := cells.filter fun c => !blocked.contains c
def region (i : Fin 36) : List Cell := match i.val with
 | 0 => without H [137,139,187,189]
 | 1 => UpperZero11.region ⟨1,by decide⟩
 | 2 => UpperZero11.region ⟨5,by decide⟩
 | 3 => UpperZero11.region ⟨2,by decide⟩
 | 4 => UpperZero11.region ⟨6,by decide⟩
 | 5 => UpperZero11.region ⟨3,by decide⟩
 | 6 => UpperZero11.region ⟨7,by decide⟩
 | 7 => PairPath11.region ⟨1,by decide⟩
 | 8 => without B [187,190]
 | 9 => without B [188,190]
 | 10 => without B [189,190]
 | 11 => without (B++[]) [187]
 | 12 => without (B++[]) [188]
 | 13 => without (B++[]) [189]
 | 14 => without B [190]
 | 15 => without (B++[]) [191]
 | 16 => without (B++[164]) [187]
 | 17 => without (B++[164]) [188]
 | 18 => without (B++[164]) [189]
 | 19 => without B [190]
 | 20 => without (B++[164]) [191]
 | 21 => B
 | 22 => without (B++[164,138]) [187]
 | 23 => without (B++[164,138]) [188]
 | 24 => without (B++[164,138]) [189]
 | 25 => without B [190]
 | 26 => without (B++[164,138]) [191]
 | 27 => B
 | 28 => B++[164]
 | 29 => without Corral11.regionBase [215,216]
 | 30 => without Corral11.regionBase [215]
 | 31 => Corral11.regionBase
 | 32 => without H [138,164]
 | 33 => without H [164,190]
 | 34 => without H [188,189]
 | _ => without H [183,184,185,186,209,210,211,212,187,213]

abbrev paid := UpperLocalPrice11.paid
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique : ∀i, (locks i).Nodup := by decide +kernel
theorem nonempty : ∀i, locks i≠[] := by decide +kernel
end Owner1007.Upper187Cover11
