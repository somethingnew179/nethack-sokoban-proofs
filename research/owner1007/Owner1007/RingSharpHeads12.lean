import Owner1007.PreRingHeads12
namespace Owner1007.RingSharpHeads12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def classified (i : Fin 4) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (PreCage12.ringLocks i) source dir ∨
 (source=263 ∧ dir=.west) ∨ (source=290 ∧ dir=.west) ∨
 (source=187 ∧ dir=.north) ∨ (source=212 ∧ dir=.west) ∨
 (source=265 ∧ dir=.south) ∨ (source=239 ∧ dir=.south) ∨
 PreRingHeads12.square i source dir
instance (i : Fin 4) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by
 unfold classified PreRingHeads12.square
 infer_instance
theorem checked : ∀ i, ∀ hero∈PreCage12.ringRegion i, ∀ dir∈allDirs,
 ∀ source∈PreRingHeads12.sources, advance soko1_2.board hero dir=some source →
 PreCage12.ringPaid source dir → classified i source dir := by decide +kernel
theorem classification (i : Fin 4) (hero : Cell) (heroIn : hero∈PreCage12.ringRegion i)
 (dir source) (sourceIn : source∈PreRingHeads12.sources)
 (adjacent : advance soko1_2.board hero dir=some source) (paid : PreCage12.ringPaid source dir) :
 classified i source dir :=
 checked i hero heroIn dir (Geometry.all_directions dir) source sourceIn adjacent paid
#print axioms classification
end Owner1007.RingSharpHeads12

