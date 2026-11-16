import Owner1007.FirstSplit12
import NetHack.Sokoban.Generated.Soko12Potential
namespace Owner1007.NorthEvents12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def base : List Cell := [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,184,185,186,187,189,190,191,192,193,194,206,211,212,213,214,215,216,218,219,220,232,239,241,242,244,245,246,258,270,271,272,284,296,297,310,322,336,348,370,371,372,373,374,396,397,399,400]
def current : Fin 5 → Cell | 0 => 345 | 1 => 319 | 2 => 293 | 3 => 292 | 4 => 291
def locks (i : Fin 5) : List Cell := [210,237,238,263,265,318,current i]
def region : Fin 5 → List Cell
 | 0 => base
 | 1 => base ++ [345]
 | 2 => base ++ [345,319,320,294]
 | 3 => base ++ [345,319,320,294,293]
 | 4 => base ++ [345,319,320,294,293,292]
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=210 ∧ dir=.south) ∨ (source=238 ∧ dir=.south) ∨
 (source=265 ∧ dir=.south) ∨ (source=318 ∧ dir=.west) ∨ (source=291 ∧ dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
def J : List Cell := [210,237,238,263,265,318]
def nodeCheck (i : Fin 5) : Bool :=
 (region i).all fun hero => allDirs.all fun dir =>
  Corral11.walkCheck soko1_2.board locks region i hero dir &&
   (locks i).all fun source => decide (advance soko1_2.board hero dir ≠ some source ∨
    BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir ∨
     Corral11.Shift soko1_2.board soko1_2.initial.holes locks region i source dir)
def GuardNode (i : Fin 5) : Prop := ∀ hero ∈ region i, ∀ dir ∈ allDirs, ∀ source ∈ J,
 advance soko1_2.board hero dir = some source →
  BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem size : ∀ i, (locks i).length=7 := by decide +kernel
theorem j_inside : ∀ i, J ⊆ locks i := by decide +kernel
theorem paid_cost : ∀ source ∈ [210,238,265,318,291], ∀ dir ∈ allDirs,
 paid source dir → ∀ dest ∈ pushTargets soko1_2.board source dir,
 dest ∉ soko1_2.initial.holes ∧
 1 + Generated.soko1_2Potential.boulder dest - Generated.soko1_2Potential.boulder source =
 (if source=318 then 3 else 2) := by decide +kernel
theorem ring_activation : pushTargets soko1_2.board 291 .west = [290] := by decide +kernel
#print axioms paid_cost
end Owner1007.NorthEvents12
