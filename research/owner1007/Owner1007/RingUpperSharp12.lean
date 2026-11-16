import Owner1007.PostUpper29112
namespace Owner1007.RingUpperSharp12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def classified (i : Fin 3) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (RingUpper12.locks i) source dir ∨
 (source=186 ∧ dir=.west) ∨ (source=161 ∧ dir=.north) ∨
 (source=212 ∧ dir=.west) ∨ (source=263 ∧ dir=.west) ∨
 (source=290 ∧ dir=.west) ∨ (source=265 ∧ dir=.south) ∨
 (source=239 ∧ dir=.south) ∨ (source=213 ∧ dir=.north) ∨ (source=213 ∧ dir=.south)
instance (i : Fin 3) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by unfold classified; infer_instance
theorem classification : ∀ i, ∀ hero∈RingUpper12.region i, ∀ dir∈allDirs,
 ∀ source∈RingUpper12.sources,
 advance soko1_2.board hero dir=some source → RingUpper12.paid source dir → classified i source dir := by decide +kernel
theorem gate : ∀ i, [158,159,185,210]⊆185::(RingUpper12.locks i).erase 186 := by decide +kernel
theorem quad : ∀ i, Quad29012.locks 0⊆211::(RingUpper12.locks i).erase 212 := by decide +kernel
theorem seven : ∀ i, Post187Seven12.locks 0⊆262::(RingUpper12.locks i).erase 263 := by decide +kernel
theorem t291 : ∀ i, PostUpper29112.locks 0⊆291::(RingUpper12.locks i).erase 265 := by decide +kernel
theorem reset : ∀ i, RingUpper12.locks 0⊆265::(RingUpper12.locks i).erase 239 := by decide +kernel
theorem trapped : ∀ i, [161,187]⊆187::(RingUpper12.locks i).erase 213 := by decide +kernel
theorem locked161187 : Locked soko1_2.board [161,187] := locked_of_check _ _ (by decide +kernel)
theorem extra_reset : ∀ i, RingUpper12.locks 1⊆239::(RingUpper12.locks i).erase 213 := by decide +kernel
#print axioms classification
#print axioms locked161187
end Owner1007.RingUpperSharp12
