import Owner1007.FastCorral11
import Owner1007.OwnedEventsMore12
import Owner1007.DeadCorridor12
namespace Owner1007.FirstFill10812
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def locks : Fin 4 → List Cell
 | 0 => [108]
 | 1 => [82]
 | 2 => [56]
 | 3 => [30]
def region : Fin 4 → List Cell
 | 0 => [105,106,115,116,117,131,132,133,134,135,140,141,142,143,157,158,159,160,161,163,164,166,167,168,169,184,185,186,187,189,190,191,192,193,194,210,211,212,213,214,215,216,218,219,220,236,237,238,239,241,242,244,245,246,262,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 1 => [105,106,108,115,116,117,131,132,133,134,135,140,141,142,143,157,158,159,160,161,163,164,166,167,168,169,184,185,186,187,189,190,191,192,193,194,210,211,212,213,214,215,216,218,219,220,236,237,238,239,241,242,244,245,246,262,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 2 => [82,105,106,108,115,116,117,131,132,133,134,135,140,141,142,143,157,158,159,160,161,163,164,166,167,168,169,184,185,186,187,189,190,191,192,193,194,210,211,212,213,214,215,216,218,219,220,236,237,238,239,241,242,244,245,246,262,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 3 => [29,55,56,82,105,106,108,115,116,117,131,132,133,134,135,140,141,142,143,157,158,159,160,161,163,164,166,167,168,169,184,185,186,187,189,190,191,192,193,194,210,211,212,213,214,215,216,218,219,220,236,237,238,239,241,242,244,245,246,262,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
def paid (source : Cell) (dir : Dir) : Prop := source=30 ∧ dir=.east
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
theorem checked : ∀ i, FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes locks region paid i=true := by decide +kernel
theorem floors : ∀ i, region i⊆soko1_2.board.floor := by decide +kernel
theorem reverse : Geometry.reverseCheck soko1_2.board=true := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ reverse floors checked
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
def fillGuardCheck (i : Fin 4) : Bool :=
 soko1_2.board.floor.all fun source=>allDirs.all fun dir=>
 match advance soko1_2.board source dir.opposite with
 | none=>true
 | some hero=>decide (hero∉region i ∨ ∀ dest∈pushTargets soko1_2.board source dir,
     dest∈soko1_2.initial.holes → source∈locks i ∧ paid source dir)
theorem fillGuard_checked : ∀ i, fillGuardCheck i=true := by decide +kernel
theorem fill_guard (i : Fin 4) (hero : Cell) (heroInside : hero∈region i)
 (dir : Dir) (source : Cell) (sourceFloor : source∈soko1_2.board.floor)
 (adjacent : advance soko1_2.board hero dir=some source) :
 ∀ dest∈pushTargets soko1_2.board source dir,
 dest∈soko1_2.initial.holes → source∈locks i ∧ paid source dir := by
 have behind := Geometry.reverseCheck_sound soko1_2.board reverse hero (floors i heroInside) dir source adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp (fillGuard_checked i) source sourceFloor) dir (Geometry.all_directions dir)
 simp only [behind] at row
 exact (of_decide_eq_true row).resolve_left (fun outside=>outside heroInside)
theorem initial_hero : soko1_2.initial.player∈region 0 := by decide +kernel
theorem initial_locks : locks 0⊆soko1_2.initial.boulders := by decide +kernel
#print axioms closed
#print axioms fill_guard
end Owner1007.FirstFill10812
