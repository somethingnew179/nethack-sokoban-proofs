/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban.Generated.Soko41Potential
namespace NetHack.Sokoban41
open NetHack.Sokoban
structure Ten where
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
  deriving DecidableEq, Repr

def support : List Cell := [30, 44, 38, 51, 52, 53, 66, 50, 49, 48]
def deadCells : List Cell := [15, 16, 17, 18, 23, 24, 25, 29, 39, 43, 53, 57, 58, 62, 67, 85, 90, 92, 96, 99, 110, 124, 138, 152, 156, 157]
def floor : List Cell := [15, 16, 17, 18, 23, 24, 25, 29, 30, 31, 32, 37, 38, 39, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 57, 58, 62, 66, 67, 80, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 99, 100, 106, 107, 108, 109, 110, 114, 120, 121, 122, 123, 124, 128, 134, 135, 136, 137, 138, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 156, 157]
def index (cell : Cell) : Nat :=
  if cell = 30 then 0 else
  if cell = 44 then 1 else
  if cell = 38 then 2 else
  if cell = 51 then 3 else
  if cell = 52 then 4 else
  if cell = 53 then 5 else
  if cell = 66 then 6 else
  if cell = 50 then 7 else
  if cell = 49 then 8 else
  if cell = 48 then 9 else
  10

def change (pattern : Ten) (clear put : Nat) : Ten := {
  a := if put = 0 then true else if clear = 0 then false else pattern.a
  b := if put = 1 then true else if clear = 1 then false else pattern.b
  c := if put = 2 then true else if clear = 2 then false else pattern.c
  d := if put = 3 then true else if clear = 3 then false else pattern.d
  e := if put = 4 then true else if clear = 4 then false else pattern.e
  f := if put = 5 then true else if clear = 5 then false else pattern.f
  g := if put = 6 then true else if clear = 6 then false else pattern.g
  h := if put = 7 then true else if clear = 7 then false else pattern.h
  i := if put = 8 then true else if clear = 8 then false else pattern.i
  j := if put = 9 then true else if clear = 9 then false else pattern.j }

def erase (pattern : Ten) (source : Cell) : Ten := change pattern (index source) 10
def insert (pattern : Ten) (destination : Cell) : Ten := change pattern 10 (index destination)
def known (pattern : Ten) (cell : Cell) : Bool :=
  if cell = 30 then pattern.a else
  if cell = 44 then pattern.b else
  if cell = 38 then pattern.c else
  if cell = 51 then pattern.d else
  if cell = 52 then pattern.e else
  if cell = 53 then pattern.f else
  if cell = 66 then pattern.g else
  if cell = 50 then pattern.h else
  if cell = 49 then pattern.i else
  if cell = 48 then pattern.j else
  false

def ofBoxes (boxes : List Cell) : Ten := {
  a := boxes.contains 30
  b := boxes.contains 44
  c := boxes.contains 38
  d := boxes.contains 51
  e := boxes.contains 52
  f := boxes.contains 53
  g := boxes.contains 66
  h := boxes.contains 50
  i := boxes.contains 49
  j := boxes.contains 48 }

def deadCount (boxes : List Cell) : Nat := (boxes.filter fun cell => deadCells.contains cell).length
def debt (cell : Cell) : Int := -NetHack.Sokoban.Generated.soko4_1Potential.boulder cell
end NetHack.Sokoban41
