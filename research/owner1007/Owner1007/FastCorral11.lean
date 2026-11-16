import Owner1007.PricedCorral11
import NetHack.Sokoban.Geometry

namespace Owner1007.FastCorral11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open Owner1007.Corral11 Owner1007.PricedCorral11

def walkCheck {n : Nat} (board : Board) (locks region : Fin n → List Cell)
    (i : Fin n) (hero : Cell) (dir : Dir) : Bool :=
  match advance board hero dir with
  | none => true
  | some target => if target ∈ region i then true else
      decide (¬ (target ∈ board.floor ∧ target ∉ board.doors ∧ target ∉ locks i ∧
        corner board (PatternCorrection.project (locks i)) hero dir = false))

def nodeCheck {n : Nat} (board : Board) (holes : List Cell) (locks region : Fin n → List Cell)
    (paid : Cell → Dir → Prop) [∀ c d, Decidable (paid c d)] (i : Fin n) : Bool :=
  ((region i).all fun hero => allDirs.all fun dir => walkCheck board locks region i hero dir) &&
  ((locks i).all fun source => allDirs.all fun dir =>
    match advance board source dir.opposite with
    | none => true
    | some hero => decide (hero ∉ region i ∨ BlockedPush board (locks i) source dir ∨
        paid source dir ∨ Shift board holes locks region i source dir))

theorem closed_of_checks {n : Nat} (board : Board) (holes : List Cell)
    (locks region : Fin n → List Cell) (paid : Cell → Dir → Prop) [∀ c d, Decidable (paid c d)]
    (reverse : Geometry.reverseCheck board = true) (floors : ∀ i, region i ⊆ board.floor)
    (checked : ∀ i, nodeCheck board holes locks region paid i = true) :
    ClosedExcept board holes locks region paid := by
  constructor
  · intro i hero heroInside dir target adjacent floor door notLock clear
    have all := (Bool.and_eq_true_iff.mp (checked i)).1
    have row := List.all_eq_true.mp (List.all_eq_true.mp all hero heroInside) dir (Geometry.all_directions dir)
    by_cases targetInside : target ∈ region i
    · exact targetInside
    · simp only [walkCheck,adjacent,if_neg targetInside] at row
      exact False.elim (of_decide_eq_true row ⟨floor,door,notLock,clear⟩)
  · intro i hero heroInside dir source sourceInside adjacent
    have all := (Bool.and_eq_true_iff.mp (checked i)).2
    have row := List.all_eq_true.mp (List.all_eq_true.mp all source sourceInside) dir (Geometry.all_directions dir)
    have behind := Geometry.reverseCheck_sound board reverse hero (floors i heroInside) dir source adjacent
    simp only [behind] at row
    exact (of_decide_eq_true row).resolve_left (fun outside => outside heroInside)

def walkPart {n : Nat} (board : Board) (locks region : Fin n → List Cell) (i : Fin n) (dir : Dir) : Bool :=
  (region i).all fun hero => walkCheck board locks region i hero dir
def pushPart {n : Nat} (board : Board) (holes : List Cell) (locks region : Fin n → List Cell)
    (paid : Cell → Dir → Prop) [∀ c d, Decidable (paid c d)] (i : Fin n) : Bool :=
  (locks i).all fun source => allDirs.all fun dir =>
    match advance board source dir.opposite with
    | none => true
    | some hero => decide (hero ∉ region i ∨ BlockedPush board (locks i) source dir ∨
        paid source dir ∨ Shift board holes locks region i source dir)

theorem node_of_parts {n : Nat} (board : Board) (holes : List Cell) (locks region : Fin n → List Cell)
    (paid : Cell → Dir → Prop) [∀ c d, Decidable (paid c d)] (i : Fin n)
    (walks : ∀ dir, walkPart board locks region i dir = true)
    (pushes : pushPart board holes locks region paid i = true) :
    nodeCheck board holes locks region paid i = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_,pushes⟩
  apply List.all_eq_true.mpr
  intro hero member
  apply List.all_eq_true.mpr
  intro dir _
  exact List.all_eq_true.mp (walks dir) hero member

#print axioms closed_of_checks
#print axioms node_of_parts
end Owner1007.FastCorral11
