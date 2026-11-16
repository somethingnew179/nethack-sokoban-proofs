import Owner1007.AfterJBound12
namespace Owner1007.After23821012
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
open Owner1007.TokenAccounting Owner1007.OwnedEvents12
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def ordinary : List Cell := [236,237,263,264,265]
def fixed : List Cell := ordinary ++ [318]
def locks (i : Fin 5) : List Cell := fixed ++ [NorthEvents12.current i]
def region (i : Fin 5) : List Cell := NorthEvents12.region i ++ [238,210]
def paid (source : Cell) (dir : Dir) : Prop :=
 ((source=236 ∨ source=264 ∨ source=265) ∧ dir=.south) ∨
 (source=318 ∧ dir=.west) ∨ (source=291 ∧ dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem size : ∀ i, (locks i).length=7 := by decide +kernel
theorem fixed_inside : ∀ i, fixed ⊆ locks i := by decide +kernel
def nodeCheck (i : Fin 5) : Bool :=
 (region i).all fun hero => allDirs.all fun dir =>
  Corral11.walkCheck soko1_2.board locks region i hero dir &&
   (locks i).all fun source => decide (advance soko1_2.board hero dir ≠ some source ∨
    BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir ∨
     Corral11.Shift soko1_2.board soko1_2.initial.holes locks region i source dir)
theorem fixed_guard : ∀ i hero, hero∈region i → ∀ dir source, source∈fixed →
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir := by
 intro i hero member dir source inside adjacent
 exact guard i hero member dir (Geometry.all_directions dir) source inside adjacent
where
 guard : ∀ i, ∀ hero∈region i, ∀ dir∈allDirs, ∀ source∈fixed,
  advance soko1_2.board hero dir=some source →
  BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir := by decide +kernel
theorem paid_cost : ∀ source∈[236,264,265,318,291], ∀ dir∈allDirs, paid source dir →
 ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧ (if source=318 then (3:Int) else 2) ≤1+p.boulder dest-p.boulder source := by decide +kernel
end Owner1007.After23821012
