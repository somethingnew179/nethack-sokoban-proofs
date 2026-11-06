/- Finite ordinary-kernel checking of arbitrary-support occupancy certificates.
Enumeration is complete for all Boolean functions on the declared support. -/
import NetHack.Sokoban.PatternCorrection
import NetHack.Sokoban.Geometry
namespace NetHack.Sokoban.PatternCorrection
open LowerBounds

def Agree (support : List Cell) (p q : Pattern) : Prop := ∀ cell, cell ∈ support → p cell = q cell

def setBit (p : Pattern) (cell : Cell) (bit : Bool) : Pattern :=
  fun c => if cell = c then bit else p c

def allPatterns : List Cell → List Pattern
  | [] => [fun _ => false]
  | cell :: cells => (allPatterns cells).flatMap fun p => [setBit p cell false, setBit p cell true]

theorem patterns_complete (support : List Cell) (pattern : Pattern) :
    ∃ representative ∈ allPatterns support, Agree support pattern representative := by
  induction support with
  | nil => exact ⟨fun _ => false, by simp [allPatterns], by simp [Agree]⟩
  | cons cell cells ih =>
    rcases ih with ⟨p, member, agree⟩
    refine ⟨setBit p cell (pattern cell), List.mem_flatMap.mpr ⟨p, member, ?_⟩, ?_⟩
    · cases pattern cell <;> simp
    · intro c h
      by_cases same : cell = c
      · simp [setBit, same]
      · have hc : c ∈ cells := (List.mem_cons.mp h).resolve_left (Ne.symm same)
        simpa [setBit, same] using agree c hc

theorem known_agree {support : List Cell} {p q : Pattern} (agree : Agree support p q) (cell : Cell) :
    known support p cell = known support q cell := by
  by_cases member : cell ∈ support
  · simp only [known, List.contains_iff_mem.mpr member, Bool.true_and]; exact agree cell member
  · simp [known, member]

theorem change_agree {support : List Cell} {p q : Pattern} (agree : Agree support p q)
    (source : Cell) (destination : Option Cell) :
    Agree support (change p source destination) (change q source destination) := by
  intro cell member
  simp only [change]
  rw [agree cell member]

def rowCheck (board : Board) (originalHoles : List Cell) (potential : Potential)
    (support : List Cell) (bonus : Cell → Pattern → Int) (player : Cell) (pattern : Pattern) : Bool :=
  allDirs.all fun direction =>
    match advance board player direction with
    | none => true
    | some source =>
      if !board.floor.contains source then true else
      ((!walkGuard board support pattern player source direction ||
        decide (bonus player pattern ≤ bonus source pattern)) &&
      (if direction.diagonal then true else
        match advance board source direction with
        | none => true
        | some first =>
          if !board.floor.contains first then true else
          (PreciseRolling.stayTargets board source direction).all (fun landing =>
            !pushGuard support pattern player source first landing ||
            decide (bonus player pattern ≤ 1 + potential.boulder landing - potential.boulder source +
              bonus source (change pattern source (some landing)))) &&
          (pushTargets board source direction).all (fun landing =>
            !originalHoles.contains landing || !pushGuard support pattern player source first landing ||
            decide (bonus player pattern ≤ 1 - potential.boulder source - potential.hole landing +
              bonus source (change pattern source none)))))

theorem rowCheck_agree (board : Board) (originalHoles : List Cell) (potential : Potential)
    (support : List Cell) (bonus : Cell → Pattern → Int)
    (respects : ∀ player p q, Agree support p q → bonus player p = bonus player q)
    (player : Cell) (p q : Pattern) (agree : Agree support p q) :
    rowCheck board originalHoles potential support bonus player p =
      rowCheck board originalHoles potential support bonus player q := by
  have knownEq : known support p = known support q := funext (known_agree agree)
  have bonusEq : (fun player => bonus player p) = (fun player => bonus player q) :=
    funext (fun player => respects player p q agree)
  have changeEq (source : Cell) (destination : Option Cell) :
      (fun player => bonus player (change p source destination)) =
      (fun player => bonus player (change q source destination)) :=
    funext (fun player => respects player _ _ (change_agree agree source destination))
  have changePointwise (source : Cell) (destination : Option Cell) (player : Cell) :
      bonus player (change p source destination) = bonus player (change q source destination) :=
    congrFun (changeEq source destination) player
  have sideEq (player : Cell) (direction : Dir) :
      relaxedSide board support p player direction = relaxedSide board support q player direction := by
    simp only [relaxedSide, relaxedBlocked, knownEq]
  simp only [rowCheck]
  congr 1
  funext direction
  cases adjacent : advance board player direction with
  | none => rfl
  | some source =>
    simp only [walkGuard, relaxedCorner, sideEq, knownEq]
    rw [congrFun bonusEq player, congrFun bonusEq source]
    congr 1
    split
    · rfl
    · cases firstAdj : advance board source direction with
      | none => rfl
      | some first =>
        simp only [pushGuard, knownEq, changePointwise, congrFun bonusEq player]

theorem checked_patterns (board : Board) (originalHoles : List Cell) (potential : Potential)
    (support : List Cell) (bonus : Cell → Pattern → Int)
    (respects : ∀ player p q, Agree support p q → bonus player p = bonus player q)
    (player : Cell)
    (checked : (allPatterns support).all (rowCheck board originalHoles potential support bonus player) = true)
    (pattern : Pattern) : rowCheck board originalHoles potential support bonus player pattern = true := by
  rcases patterns_complete support pattern with ⟨p, member, agree⟩
  rw [rowCheck_agree board originalHoles potential support bonus respects player pattern p agree]
  exact List.all_eq_true.mp checked p member

theorem row_walk {board originalHoles potential support bonus player pattern}
    (checked : rowCheck board originalHoles potential support bonus player pattern = true)
    (direction : Dir) (target : Cell) (adjacent : advance board player direction = some target)
    (floor : target ∈ board.floor)
    (guard : walkGuard board support pattern player target direction = true) :
    bonus player pattern ≤ bonus target pattern := by
  have edge := List.all_eq_true.mp checked direction (Geometry.all_directions direction)
  simp only [adjacent, List.contains_iff_mem.mpr floor, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    guard, Bool.false_or, Bool.and_eq_true_iff, decide_eq_true_eq] at edge
  exact edge.1

private theorem row_pushes {board originalHoles potential support bonus player pattern}
    (checked : rowCheck board originalHoles potential support bonus player pattern = true)
    (direction : Dir) (source first : Cell) (diagonal : direction.diagonal = false)
    (adjacent : advance board player direction = some source) (floor : source ∈ board.floor)
    (firstAdj : advance board source direction = some first) (firstFloor : first ∈ board.floor) :
    (PreciseRolling.stayTargets board source direction).all (fun landing =>
      !pushGuard support pattern player source first landing ||
      decide (bonus player pattern ≤ 1 + potential.boulder landing - potential.boulder source +
        bonus source (change pattern source (some landing)))) = true ∧
    (pushTargets board source direction).all (fun landing =>
      !originalHoles.contains landing || !pushGuard support pattern player source first landing ||
      decide (bonus player pattern ≤ 1 - potential.boulder source - potential.hole landing +
        bonus source (change pattern source none))) = true := by
  have edge := List.all_eq_true.mp checked direction (Geometry.all_directions direction)
  simp only [adjacent, List.contains_iff_mem.mpr floor, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    diagonal, firstAdj, List.contains_iff_mem.mpr firstFloor, Bool.and_eq_true_iff] at edge
  exact edge.2

theorem row_stay {board originalHoles potential support bonus player pattern}
    (checked : rowCheck board originalHoles potential support bonus player pattern = true)
    (direction : Dir) (source first landing : Cell) (diagonal : direction.diagonal = false)
    (adjacent : advance board player direction = some source) (floor : source ∈ board.floor)
    (firstAdj : advance board source direction = some first) (firstFloor : first ∈ board.floor)
    (target : landing ∈ PreciseRolling.stayTargets board source direction)
    (guard : pushGuard support pattern player source first landing = true) :
    bonus player pattern ≤ 1 + potential.boulder landing - potential.boulder source +
      bonus source (change pattern source (some landing)) := by
  have h := List.all_eq_true.mp (row_pushes checked direction source first diagonal adjacent floor firstAdj firstFloor).1 landing target
  simpa only [guard, Bool.not_true, Bool.false_or, decide_eq_true_eq] using h

theorem row_consume {board originalHoles potential support bonus player pattern}
    (checked : rowCheck board originalHoles potential support bonus player pattern = true)
    (direction : Dir) (source first landing : Cell) (diagonal : direction.diagonal = false)
    (adjacent : advance board player direction = some source) (floor : source ∈ board.floor)
    (firstAdj : advance board source direction = some first) (firstFloor : first ∈ board.floor)
    (target : landing ∈ pushTargets board source direction) (hole : landing ∈ originalHoles)
    (guard : pushGuard support pattern player source first landing = true) :
    bonus player pattern ≤ 1 - potential.boulder source - potential.hole landing +
      bonus source (change pattern source none) := by
  have h := List.all_eq_true.mp (row_pushes checked direction source first diagonal adjacent floor firstAdj firstFloor).2 landing target
  simpa only [List.contains_iff_mem.mpr hole, guard, Bool.not_true, Bool.false_or, decide_eq_true_eq] using h
def goalCheck (support : List Cell) (allowance : Nat) (potential : Potential)
    (value : Pattern → Int) (pattern : Pattern) : Bool :=
  decide ((support.filter pattern).length ≤ allowance →
    value pattern ≤ weightSum (fun cell => -potential.boulder cell) (support.filter pattern))

theorem checked_goal (support : List Cell) (allowance : Nat) (potential : Potential)
    (value : Pattern → Int) (respects : ∀ p q, Agree support p q → value p = value q)
    (checked : (allPatterns support).all (goalCheck support allowance potential value) = true)
    (pattern : Pattern) (budget : (support.filter pattern).length ≤ allowance) :
    value pattern ≤ weightSum (fun cell => -potential.boulder cell) (support.filter pattern) := by
  rcases patterns_complete support pattern with ⟨p, member, agree⟩
  have filtered : support.filter pattern = support.filter p := by
    apply List.filter_congr
    intro cell present
    exact agree cell present
  have bound := List.all_eq_true.mp checked p member
  simp only [goalCheck, decide_eq_true_eq] at bound
  rw [respects pattern p agree, filtered]
  exact bound (by simpa only [filtered] using budget)
theorem nonnegative_ite (condition : Bool) {a b : Int} (first : 0 ≤ a) (second : 0 ≤ b) :
    0 ≤ (if condition then a else b) := by cases condition <;> assumption

theorem upper_ite (condition : Bool) {a b bound : Int} (first : a ≤ bound) (second : b ≤ bound) :
    (if condition then a else b) ≤ bound := by cases condition <;> assumption
end NetHack.Sokoban.PatternCorrection
