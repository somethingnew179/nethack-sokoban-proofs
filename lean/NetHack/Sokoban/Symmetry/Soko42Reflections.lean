/- Actual normalized soko4-2 reflections. Each geometric premise is checked
on all165 rectangle cells and all8 directions. Directions/cells are global
involutions; generic semantics transfer proves equal costs for every trace. -/
import NetHack.Sokoban.Symmetry.FiniteGeometry
import NetHack.Sokoban.Soko42Optimal

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace NetHack.Sokoban.Symmetry.Soko42Reflections

def horizontalTable : List Cell := [14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 104, 103, 102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 134, 133, 132, 131, 130, 129, 128, 127, 126, 125, 124, 123, 122, 121, 120, 149, 148, 147, 146, 145, 144, 143, 142, 141, 140, 139, 138, 137, 136, 135, 164, 163, 162, 161, 160, 159, 158, 157, 156, 155, 154, 153, 152, 151, 150]

def horizontalDir : Dir → Dir
  | .north => .north
  | .south => .south
  | .east => .west
  | .west => .east
  | .northEast => .northWest
  | .northWest => .northEast
  | .southEast => .southWest
  | .southWest => .southEast

def horizontalDirections : DirectionPermutation := {
  apply := horizontalDir
  involutive := by intro direction; cases direction <;> rfl
  diagonal := by intro direction; cases direction <;> rfl
  opposite := by intro direction; cases direction <;> rfl
  sides := by
    intro direction diagonal
    cases direction <;> simp_all [horizontalDir, Dir.diagonal, Dir.sides] }

theorem horizontal_permutation_checked : permutationCheck horizontalTable = true := by decide

def horizontalCells : CellPermutation := ofTable horizontalTable horizontal_permutation_checked

theorem horizontal_geometry_checked : advanceCheck soko4_2.board horizontalCells horizontalDirections = true := by decide

def horizontal : BoardIsomorphism soko4_2.board :=
  finiteIsomorphism soko4_2.board horizontalTable horizontal_permutation_checked
    (by decide) horizontalDirections horizontal_geometry_checked

def verticalTable : List Cell := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

def verticalDir : Dir → Dir
  | .north => .south
  | .south => .north
  | .east => .east
  | .west => .west
  | .northEast => .southEast
  | .northWest => .southWest
  | .southEast => .northEast
  | .southWest => .northWest

def verticalDirections : DirectionPermutation := {
  apply := verticalDir
  involutive := by intro direction; cases direction <;> rfl
  diagonal := by intro direction; cases direction <;> rfl
  opposite := by intro direction; cases direction <;> rfl
  sides := by
    intro direction diagonal
    cases direction <;> simp_all [verticalDir, Dir.diagonal, Dir.sides] }

theorem vertical_permutation_checked : permutationCheck verticalTable = true := by decide

def verticalCells : CellPermutation := ofTable verticalTable vertical_permutation_checked

theorem vertical_geometry_checked : advanceCheck soko4_2.board verticalCells verticalDirections = true := by decide

def vertical : BoardIsomorphism soko4_2.board :=
  finiteIsomorphism soko4_2.board verticalTable vertical_permutation_checked
    (by decide) verticalDirections vertical_geometry_checked

def bothTable : List Cell := [164, 163, 162, 161, 160, 159, 158, 157, 156, 155, 154, 153, 152, 151, 150, 149, 148, 147, 146, 145, 144, 143, 142, 141, 140, 139, 138, 137, 136, 135, 134, 133, 132, 131, 130, 129, 128, 127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

def bothDir : Dir → Dir
  | .north => .south
  | .south => .north
  | .east => .west
  | .west => .east
  | .northEast => .southWest
  | .northWest => .southEast
  | .southEast => .northWest
  | .southWest => .northEast

def bothDirections : DirectionPermutation := {
  apply := bothDir
  involutive := by intro direction; cases direction <;> rfl
  diagonal := by intro direction; cases direction <;> rfl
  opposite := by intro direction; cases direction <;> rfl
  sides := by
    intro direction diagonal
    cases direction <;> simp_all [bothDir, Dir.diagonal, Dir.sides] }

theorem both_permutation_checked : permutationCheck bothTable = true := by decide

def bothCells : CellPermutation := ofTable bothTable both_permutation_checked

theorem both_geometry_checked : advanceCheck soko4_2.board bothCells bothDirections = true := by decide

def both : BoardIsomorphism soko4_2.board :=
  finiteIsomorphism soko4_2.board bothTable both_permutation_checked
    (by decide) bothDirections both_geometry_checked

end NetHack.Sokoban.Symmetry.Soko42Reflections
