import Owner1007.After264Pre187Bound12
namespace Owner1007.CriticalWithout18712
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev Core := After264Pre18712.Core
def fixed : List Cell := Core++[211,318]
def locks (i : Fin 5) : List Cell := fixed++[NorthEvents12.current i]
def region (i : Fin 5) : List Cell := After264Pre18712.region i++[187]
def paid (source : Cell) (dir : Dir) : Prop := source∈Core∨(source=318∧dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
/-- Five existing lower words with187 erased; upper187 may move freely. -/
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem size : ∀i,(locks i).length=8 := by decide +kernel
theorem hero264 : ∀i,(264:Cell)∈region i := by decide +kernel
theorem fixed_inside : ∀i,Core⊆locks i := by decide +kernel
theorem fixed_guard : ∀i,∀hero∈region i,∀dir∈allDirs,∀source∈Core,
 advance soko1_2.board hero dir=some source→BlockedPush soko1_2.board (locks i) source dir∨paid source dir := by decide +kernel

def priceTwo (source : Cell) (dir : Dir) : Prop :=
 ∀dest∈pushTargets soko1_2.board source dir,dest∉soko1_2.initial.holes∧(2:Int)≤1+p.boulder dest-p.boulder source
instance (source : Cell) (dir : Dir) : Decidable (priceTwo source dir) := by unfold priceTwo;infer_instance
def classified (i : Fin 5) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (locks i) source dir∨(source∈Core∧priceTwo source dir)∨(source=318∧dir=.west)
instance (i : Fin 5) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by unfold classified;infer_instance
theorem classification : ∀i,∀hero∈region i,∀dir∈allDirs,∀source∈locks i,
 advance soko1_2.board hero dir=some source→paid source dir→
 classified i source dir := by decide +kernel
#print axioms matrix
#print axioms classification
end Owner1007.CriticalWithout18712
