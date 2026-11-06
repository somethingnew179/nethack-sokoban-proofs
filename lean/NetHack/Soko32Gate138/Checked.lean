import NetHack.Soko32Gate138.BitRows00
import NetHack.Soko32Gate138.BitRows01
import NetHack.Soko32Gate138.BitRows02
import NetHack.Soko32Gate138.BitRows03
import NetHack.Soko32Gate138.BitRows04
import NetHack.Soko32Gate138.BitRows05
import NetHack.Soko32Gate138.BitRows06
import NetHack.Soko32Gate138.BitRows07
import NetHack.Soko32Gate138.BitRows08
import NetHack.Soko32Gate138.BitRows09
import NetHack.Soko32Gate138.BitRows10
import NetHack.Soko32Gate138.BitRows11
import NetHack.Soko32Gate138.BitRows12
import NetHack.Soko32Gate138.BitRows13
import NetHack.Soko32Gate138.BitRows14
namespace NetHack.Soko32Gate138
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection NetHack.Sokoban.LowerBounds
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked_bits : soko3_2.board.floor.all (fun hero =>
    (allPatterns gateSupport).all (rowCheck soko3_2.board soko3_2.initial.holes localPotential gateSupport gate hero)) = true := by
  have partition : soko3_2.board.floor = heroes00 ++ heroes01 ++ heroes02 ++ heroes03 ++ heroes04 ++ heroes05 ++ heroes06 ++ heroes07 ++ heroes08 ++ heroes09 ++ heroes10 ++ heroes11 ++ heroes12 ++ heroes13 ++ heroes14 := by decide +kernel
  rw [partition]
  simp only [List.all_append,checked00,checked01,checked02,checked03,checked04,checked05,checked06,checked07,checked08,checked09,checked10,checked11,checked12,checked13,checked14,Bool.and_self]
theorem checked_strict : strictCheck = true := by decide +kernel
theorem checked_fill : fillCheck = true := by decide +kernel
theorem gate_rows (hero : Cell) (floor : hero ∈ soko3_2.board.floor) (p : Pattern) :
    rowCheck soko3_2.board soko3_2.initial.holes localPotential gateSupport gate hero p = true :=
  checked_patterns _ _ _ _ _ gate_respects hero (List.all_eq_true.mp checked_bits hero floor) p
theorem strict_frame (hero : Cell) (floor : hero ∈ soko3_2.board.floor) (direction : Dir)
    (adjacent : advance soko3_2.board hero direction = some 244) (diagonal : direction.diagonal = false)
    (outside : hero ∉ pocket) (landing : Cell) (target : landing ∈ PreciseRolling.stayTargets soko3_2.board 244 direction) :
    hero ∈ ([243,245,270] : List Cell) ∧ landing ∉ prior.support ∧
      2 ≤ 1 + potential.boulder landing - potential.boulder 244 := by
  have checked := List.all_eq_true.mp (List.all_eq_true.mp checked_strict hero floor)
    direction (Geometry.all_directions direction)
  simp only [strictCheck,if_pos (And.intro adjacent (And.intro diagonal outside))] at checked
  have pieces := Bool.and_eq_true_iff.mp checked
  exact ⟨of_decide_eq_true pieces.1,of_decide_eq_true (List.all_eq_true.mp pieces.2 landing target)⟩
theorem no244_fill (direction : Dir) (landing : Cell)
    (target : landing ∈ pushTargets soko3_2.board 244 direction) (hole : landing ∈ soko3_2.initial.holes) : False :=
  (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked_fill direction
    (Geometry.all_directions direction)) landing target)) hole
end NetHack.Soko32Gate138
