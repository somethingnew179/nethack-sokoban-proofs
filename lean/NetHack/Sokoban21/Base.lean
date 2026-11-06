/- Staged soko2-1 certificate; full109notclaimed until all fields close. -/
import NetHack.Sokoban.Generated.Soko21Potential
namespace NetHack.Sokoban21
open NetHack.Sokoban
structure Twelve where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  e : Bool
  f : Bool
  g : Bool
  h : Bool
  i : Bool
  j : Bool
  k : Bool
  l : Bool
  deriving DecidableEq, Repr

def support : List Cell := [183, 145, 65, 45, 48, 68, 126, 47, 67, 66, 70, 71]
def deadCells : List Cell := [21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 34, 35, 36, 37, 38, 41, 52, 54, 55, 56, 57, 58, 61, 72, 74, 75, 76, 77, 78, 84, 85, 92, 94, 95, 96, 97, 98, 101, 103, 106, 112, 114, 115, 116, 117, 118, 121, 125, 127, 131, 134, 135, 136, 137, 138, 141, 148, 149, 150, 154, 155, 156, 157, 158, 181, 198, 201, 202, 203, 205, 206]
def floor : List Cell := [21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 34, 35, 36, 37, 38, 41, 42, 43, 44, 45, 47, 48, 50, 52, 54, 55, 56, 57, 58, 61, 62, 64, 65, 66, 67, 68, 70, 71, 72, 74, 75, 76, 77, 78, 82, 84, 85, 87, 88, 90, 92, 94, 95, 96, 97, 98, 101, 102, 103, 106, 107, 108, 109, 110, 111, 112, 114, 115, 116, 117, 118, 121, 122, 123, 125, 126, 127, 129, 130, 131, 134, 135, 136, 137, 138, 141, 142, 143, 145, 146, 148, 149, 150, 154, 155, 156, 157, 158, 162, 163, 165, 166, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 201, 202, 203, 205, 206]
def index (cell : Cell) : Nat :=
  if cell = 183 then 0 else
  if cell = 145 then 1 else
  if cell = 65 then 2 else
  if cell = 45 then 3 else
  if cell = 48 then 4 else
  if cell = 68 then 5 else
  if cell = 126 then 6 else
  if cell = 47 then 7 else
  if cell = 67 then 8 else
  if cell = 66 then 9 else
  if cell = 70 then 10 else
  if cell = 71 then 11 else
  12

def change (pattern : Twelve) (clear put : Nat) : Twelve := {
  a := if put = 0 then true else if clear = 0 then false else pattern.a
  b := if put = 1 then true else if clear = 1 then false else pattern.b
  c := if put = 2 then true else if clear = 2 then false else pattern.c
  d := if put = 3 then true else if clear = 3 then false else pattern.d
  e := if put = 4 then true else if clear = 4 then false else pattern.e
  f := if put = 5 then true else if clear = 5 then false else pattern.f
  g := if put = 6 then true else if clear = 6 then false else pattern.g
  h := if put = 7 then true else if clear = 7 then false else pattern.h
  i := if put = 8 then true else if clear = 8 then false else pattern.i
  j := if put = 9 then true else if clear = 9 then false else pattern.j
  k := if put = 10 then true else if clear = 10 then false else pattern.k
  l := if put = 11 then true else if clear = 11 then false else pattern.l }

def erase (pattern : Twelve) (source : Cell) : Twelve := change pattern (index source) 12
def insert (pattern : Twelve) (destination : Cell) : Twelve := change pattern 12 (index destination)
def known (pattern : Twelve) (cell : Cell) : Bool :=
  if cell = 183 then pattern.a else
  if cell = 145 then pattern.b else
  if cell = 65 then pattern.c else
  if cell = 45 then pattern.d else
  if cell = 48 then pattern.e else
  if cell = 68 then pattern.f else
  if cell = 126 then pattern.g else
  if cell = 47 then pattern.h else
  if cell = 67 then pattern.i else
  if cell = 66 then pattern.j else
  if cell = 70 then pattern.k else
  if cell = 71 then pattern.l else
  false

def ofBoxes (boxes : List Cell) : Twelve := {
  a := boxes.contains 183
  b := boxes.contains 145
  c := boxes.contains 65
  d := boxes.contains 45
  e := boxes.contains 48
  f := boxes.contains 68
  g := boxes.contains 126
  h := boxes.contains 47
  i := boxes.contains 67
  j := boxes.contains 66
  k := boxes.contains 70
  l := boxes.contains 71 }

def deadCount (boxes : List Cell) : Nat := (boxes.filter fun cell => deadCells.contains cell).length
def debt (cell : Cell) : Int := -NetHack.Sokoban.Generated.soko2_1Potential.boulder cell
/-- All12supportcellsarelive; noextra known-dead budget guard is necessary. -/
def budgetGuard (_dead : Nat) (_pattern : Twelve) : Bool := true
end NetHack.Sokoban21
