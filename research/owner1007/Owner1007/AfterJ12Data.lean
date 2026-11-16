import Owner1007.NorthEvents12
import NetHack.Sokoban.Generated.Soko12Potential
namespace Owner1007.AfterJ12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def ordinary (kind : Fin 2) : List Cell :=
 if kind.val=0 then [236,237,238,263,265] else [210,237,264,263,265]
def fixed (kind : Fin 2) : List Cell := ordinary kind ++ [318]
def locks (kind : Fin 2) (i : Fin 5) : List Cell := fixed kind ++ [NorthEvents12.current i]
def region (kind : Fin 2) (i : Fin 5) : List Cell :=
 NorthEvents12.region i ++ [if kind.val=0 then 210 else 238]
def ordinaryPaid (source : Cell) (dir : Dir) : Prop :=
 ((source=210 ∨ source=236 ∨ source=238 ∨ source=264 ∨ source=265) ∧ dir=.south) ∨
 (source=237 ∧ dir=.west)
def paid (kind : Fin 2) (source : Cell) (dir : Dir) : Prop :=
 (source ∈ ordinary kind ∧ ordinaryPaid source dir) ∨
 (source=318 ∧ dir=.west) ∨ (source=291 ∧ dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (ordinaryPaid source dir) := by unfold ordinaryPaid; infer_instance
instance (kind : Fin 2) (source : Cell) (dir : Dir) : Decidable (paid kind source dir) := by unfold paid; infer_instance


def nodeCheck (kind : Fin 2) (i : Fin 5) : Bool :=
 (region kind i).all fun hero => allDirs.all fun dir =>
  Corral11.walkCheck soko1_2.board (locks kind) (region kind) i hero dir &&
   (locks kind i).all fun source => decide (advance soko1_2.board hero dir ≠ some source ∨
    BlockedPush soko1_2.board (locks kind i) source dir ∨ paid kind source dir ∨
     Corral11.Shift soko1_2.board soko1_2.initial.holes (locks kind) (region kind) i source dir)
theorem unique : ∀ kind i, (locks kind i).Nodup := by decide +kernel
theorem size : ∀ kind i, (locks kind i).length=7 := by decide +kernel
theorem fixed_inside : ∀ kind i, fixed kind ⊆ locks kind i := by decide +kernel
theorem fixed_guard_check : ∀ kind i, ∀ hero ∈ region kind i, ∀ dir ∈ allDirs, ∀ source ∈ fixed kind,
    advance soko1_2.board hero dir = some source →
      BlockedPush soko1_2.board (locks kind i) source dir ∨ paid kind source dir := by decide +kernel
theorem fixed_guard (kind : Fin 2) : ∀ i hero, hero ∈ region kind i → ∀ dir source, source ∈ fixed kind →
    advance soko1_2.board hero dir = some source →
      BlockedPush soko1_2.board (locks kind i) source dir ∨ paid kind source dir := by
  intro i hero heroInside dir source member adjacent
  exact fixed_guard_check kind i hero heroInside dir (Geometry.all_directions dir) source member adjacent
theorem paid_cost : ∀ kind, ∀ source ∈ [210,236,237,238,264,265,318,291], ∀ dir ∈ allDirs,
 paid kind source dir → ∀ dest ∈ pushTargets soko1_2.board source dir,
 dest ∉ soko1_2.initial.holes ∧
 (if source=318 then (3:Int) else 2) ≤
 1 + Generated.soko1_2Potential.boulder dest - Generated.soko1_2Potential.boulder source := by decide +kernel
#print axioms fixed_guard
def ringLocks (kind : Fin 2) (_ : Fin 1) : List Cell :=
 if kind.val=0 then [236,237,263,290] else [210,237,263,290]
def ringOutside (kind : Fin 2) : List Cell :=
 if kind.val=0 then [262,288,289] else [236,262,288,289]
def ringRegion (kind : Fin 2) (i : Fin 1) : List Cell :=
 soko1_2.board.floor.filter fun c => !(ringOutside kind).contains c && !(ringLocks kind i).contains c
def ringPaid (kind : Fin 2) (source : Cell) (dir : Dir) : Prop :=
 (kind.val=0 ∧ source=236 ∧ dir=.south) ∨
 (kind.val=1 ∧ source=210 ∧ dir=.south) ∨
 (kind.val=1 ∧ source=237 ∧ dir=.west) ∨
 (source=263 ∧ dir=.west) ∨ (source=290 ∧ dir=.west)
instance (kind : Fin 2) (source : Cell) (dir : Dir) : Decidable (ringPaid kind source dir) := by unfold ringPaid; infer_instance

theorem ringUnique : ∀ kind i, (ringLocks kind i).Nodup := by decide +kernel
theorem ringLarge : ∀ kind i, 2 < (ringLocks kind i).length := by decide +kernel
theorem ringActivation : ∀ kind i, ringLocks kind 0 ⊆ 290::(locks kind i).erase 291 := by decide +kernel
theorem ringHero : ∀ kind, 291 ∈ ringRegion kind 0 := by decide +kernel
theorem ringCost : ∀ kind, ∀ source ∈ [236,210,237,263,290], ∀ dir ∈ allDirs,
 ringPaid kind source dir → ∀ dest ∈ pushTargets soko1_2.board source dir,
 dest ∉ soko1_2.initial.holes ∧
 1 + Generated.soko1_2Potential.boulder dest - Generated.soko1_2Potential.boulder source = 2 := by decide +kernel

#print axioms ringCost
end Owner1007.AfterJ12

