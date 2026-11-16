import Owner1007.NorthEvents12
import Owner1007.CageFour12
namespace Owner1007.After264Pre18712
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def Core : List Cell := [210,237,263,265,290]
def fixed : List Cell := Core++[211,187,318]
def locks (i : Fin 5) : List Cell := fixed++[NorthEvents12.current i]
-- Five manually specified boulder footprints. Lists contain walking cells only.
def region : Fin 5 → List Cell
 | 0 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,184,185,186,189,190,191,192,193,194,206,212,213,214,215,216,218,219,220,232,238,239,241,242,244,245,246,258,264,270,271,272,284,296,297,310,322,336,348,370,371,372,373,374,396,397,399,400]
 | 1 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,184,185,186,189,190,191,192,193,194,206,212,213,214,215,216,218,219,220,232,238,239,241,242,244,245,246,258,264,270,271,272,284,296,297,310,322,336,345,348,370,371,372,373,374,396,397,399,400]
 | 2 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,184,185,186,189,190,191,192,193,194,206,212,213,214,215,216,218,219,220,232,238,239,241,242,244,245,246,258,264,270,271,272,284,294,296,297,310,319,320,322,336,345,348,370,371,372,373,374,396,397,399,400]
 | 3 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,184,185,186,189,190,191,192,193,194,206,212,213,214,215,216,218,219,220,232,238,239,241,242,244,245,246,258,264,270,271,272,284,293,294,296,297,310,319,320,322,336,345,348,370,371,372,373,374,396,397,399,400]
 | 4 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,184,185,186,189,190,191,192,193,194,206,212,213,214,215,216,218,219,220,232,238,239,241,242,244,245,246,258,264,270,271,272,284,292,293,294,296,297,310,319,320,322,336,345,348,370,371,372,373,374,396,397,399,400]
def paid (source : Cell) (dir : Dir) : Prop := source∈Core ∨source=187 ∨(source=318∧dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem size : ∀ i,(locks i).length=9 := by decide +kernel
theorem hero264 : ∀ i,(264:Cell)∈region i := by decide +kernel
theorem fixed_inside : ∀ i,fixed⊆locks i := by decide +kernel
theorem fixed_guard : ∀ i,∀ hero∈region i,∀ dir∈allDirs,∀ source∈fixed,
 advance soko1_2.board hero dir=some source→BlockedPush soko1_2.board (locks i) source dir∨paid source dir := by decide +kernel
def priceTwo (source : Cell) (dir : Dir) : Prop :=
 ∀ dest∈pushTargets soko1_2.board source dir,dest∉soko1_2.initial.holes∧(2:Int)≤1+p.boulder dest-p.boulder source
instance (source : Cell) (dir : Dir) : Decidable (priceTwo source dir) := by unfold priceTwo;infer_instance
def classified (i : Fin 5) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (locks i) source dir ∨
 (source∈Core∧priceTwo source dir) ∨(source=187∧(dir=.north∨dir=.south)) ∨(source=318∧dir=.west)
instance (i : Fin 5) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by unfold classified;infer_instance
theorem classification : ∀ i,∀ hero∈region i,∀ dir∈allDirs,∀ source∈locks i,
 advance soko1_2.board hero dir=some source→paid source dir→classified i source dir := by decide +kernel
#print axioms matrix
#print axioms classification
end Owner1007.After264Pre18712
