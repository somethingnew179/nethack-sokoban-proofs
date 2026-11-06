/- Finite nine-cell occupancy certificate for the genuine soko4-2 board.
The external pattern experiment proposes this bonus; finite Lean checks and
separate actual-step projection are the proof boundary. -/
import NetHack.Sokoban.Generated.Soko42Potential
import NetHack.Sokoban.NonlinearFacts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace NetHack.Sokoban.PatternCertificate
open LowerBounds

structure Nine where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  e : Bool
  f : Bool
  g : Bool
  h : Bool
  i : Bool
  deriving Repr, BEq, DecidableEq

def support : List Cell := [35,36,51,52,37,127,128,129,130]

def known (pattern : Nine) (cell : Cell) : Bool :=
  if cell = 35 then pattern.a else if cell = 36 then pattern.b else
  if cell = 51 then pattern.c else if cell = 52 then pattern.d else
  if cell = 37 then pattern.e else if cell = 127 then pattern.f else
  if cell = 128 then pattern.g else if cell = 129 then pattern.h else
  if cell = 130 then pattern.i else false

def ofBoxes (boxes : List Cell) : Nine :=
  ⟨boxes.contains 35, boxes.contains 36, boxes.contains 51,
   boxes.contains 52, boxes.contains 37, boxes.contains 127,
   boxes.contains 128, boxes.contains 129, boxes.contains 130⟩

def erase (pattern : Nine) (source : Cell) : Nine :=
  ⟨pattern.a && decide (source ≠ 35), pattern.b && decide (source ≠ 36),
   pattern.c && decide (source ≠ 51), pattern.d && decide (source ≠ 52),
   pattern.e && decide (source ≠ 37), pattern.f && decide (source ≠ 127),
   pattern.g && decide (source ≠ 128), pattern.h && decide (source ≠ 129),
   pattern.i && decide (source ≠ 130)⟩

def insert (pattern : Nine) (destination : Cell) : Nine :=
  ⟨pattern.a || decide (destination = 35), pattern.b || decide (destination = 36),
   pattern.c || decide (destination = 51), pattern.d || decide (destination = 52),
   pattern.e || decide (destination = 37), pattern.f || decide (destination = 127),
   pattern.g || decide (destination = 128), pattern.h || decide (destination = 129),
   pattern.i || decide (destination = 130)⟩

def one (value : Bool) : Int := if value then 1 else 0

def gate (pattern : Nine) : Bool := pattern.a && pattern.b && pattern.c && (pattern.d || pattern.e)
def leftPair (pattern : Nine) : Bool := pattern.f && pattern.g
def rightPair (pattern : Nine) : Bool := pattern.h && pattern.i

def bonus (pattern : Nine) : Int := one (gate pattern) + 2 * one (leftPair pattern) + 2 * one (rightPair pattern)
def bonusOfBoxes (boxes : List Cell) : Int := bonus (ofBoxes boxes)
def Subset (left right : Nine) : Prop := ∀ cell, known left cell = true → known right cell = true

def occupied (pattern : Nine) : List Cell := support.filter (known pattern)
def debt (cell : Cell) : Int := -Generated.soko4_2Potential.boulder cell

structure Edge where
  player : Cell
  source : Cell
  first : Cell
  landing : Cell
  direction : Dir
  moveSlack : Int
  consumeSlack : Int
  deriving Repr, DecidableEq

def edges : List Edge := [
  ⟨16,31,46,46,.south,1,1⟩,
  ⟨18,19,20,20,.east,1,1⟩,
  ⟨19,20,21,21,.east,1,1⟩,
  ⟨19,34,49,49,.south,1,1⟩,
  ⟨20,35,50,50,.south,1,1⟩,
  ⟨20,19,18,18,.west,1,1⟩,
  ⟨21,36,51,51,.south,1,1⟩,
  ⟨21,20,19,19,.west,1,1⟩,
  ⟨25,26,27,27,.east,1,1⟩,
  ⟨25,40,55,55,.south,0,5⟩,
  ⟨26,27,28,28,.east,1,1⟩,
  ⟨26,41,56,56,.south,0,4⟩,
  ⟨27,42,57,57,.south,0,3⟩,
  ⟨27,26,25,25,.west,1,1⟩,
  ⟨28,43,58,58,.south,1,1⟩,
  ⟨28,27,26,26,.west,1,1⟩,
  ⟨31,46,61,61,.south,1,1⟩,
  ⟨34,35,36,36,.east,1,1⟩,
  ⟨34,49,64,64,.south,1,1⟩,
  ⟨35,36,37,37,.east,0,1⟩,
  ⟨35,50,65,65,.south,1,1⟩,
  ⟨36,37,38,38,.east,0,2⟩,
  ⟨36,51,66,66,.south,1,1⟩,
  ⟨36,35,34,34,.west,1,1⟩,
  ⟨37,38,39,39,.east,0,3⟩,
  ⟨37,52,67,67,.south,1,1⟩,
  ⟨37,36,35,35,.west,1,1⟩,
  ⟨38,39,40,40,.east,0,4⟩,
  ⟨38,37,36,36,.west,2,2⟩,
  ⟨39,40,41,41,.east,2,5⟩,
  ⟨39,54,69,69,.south,0,7⟩,
  ⟨39,38,37,37,.west,2,3⟩,
  ⟨40,41,42,42,.east,2,4⟩,
  ⟨40,55,70,70,.south,0,6⟩,
  ⟨40,39,38,38,.west,2,4⟩,
  ⟨41,42,43,43,.east,3,3⟩,
  ⟨41,56,71,71,.south,0,5⟩,
  ⟨41,40,39,39,.west,2,5⟩,
  ⟨42,57,72,72,.south,0,4⟩,
  ⟨42,41,40,40,.west,0,4⟩,
  ⟨43,58,73,73,.south,1,1⟩,
  ⟨43,42,41,41,.west,0,3⟩,
  ⟨46,31,16,16,.north,16,16⟩,
  ⟨46,61,76,76,.south,1,1⟩,
  ⟨49,34,19,19,.north,1,1⟩,
  ⟨49,50,51,51,.east,1,1⟩,
  ⟨50,35,20,20,.north,1,1⟩,
  ⟨50,51,52,52,.east,1,1⟩,
  ⟨51,36,21,21,.north,1,1⟩,
  ⟨51,50,49,49,.west,1,1⟩,
  ⟨52,51,50,50,.west,1,1⟩,
  ⟨54,55,56,56,.east,2,6⟩,
  ⟨54,69,84,84,.south,0,8⟩,
  ⟨55,40,25,25,.north,5,5⟩,
  ⟨55,56,57,57,.east,2,5⟩,
  ⟨56,41,26,26,.north,4,4⟩,
  ⟨56,57,58,58,.east,4,4⟩,
  ⟨56,55,54,54,.west,0,6⟩,
  ⟨57,42,27,27,.north,3,3⟩,
  ⟨57,56,55,55,.west,0,5⟩,
  ⟨58,43,28,28,.north,1,1⟩,
  ⟨58,57,56,56,.west,0,4⟩,
  ⟨61,46,31,31,.north,1,1⟩,
  ⟨61,76,91,91,.south,1,1⟩,
  ⟨64,49,34,34,.north,1,1⟩,
  ⟨64,65,66,66,.east,1,1⟩,
  ⟨65,50,35,35,.north,1,1⟩,
  ⟨65,66,67,67,.east,1,1⟩,
  ⟨66,51,36,36,.north,1,1⟩,
  ⟨66,65,64,64,.west,1,1⟩,
  ⟨67,52,37,37,.north,0,1⟩,
  ⟨67,66,65,65,.west,1,1⟩,
  ⟨69,54,39,39,.north,4,7⟩,
  ⟨69,70,71,71,.east,2,7⟩,
  ⟨69,84,99,99,.south,0,9⟩,
  ⟨70,55,40,40,.north,2,6⟩,
  ⟨70,71,72,72,.east,2,6⟩,
  ⟨71,56,41,41,.north,2,5⟩,
  ⟨71,72,73,73,.east,5,5⟩,
  ⟨71,70,69,69,.west,0,7⟩,
  ⟨72,57,42,42,.north,2,4⟩,
  ⟨72,71,70,70,.west,0,6⟩,
  ⟨73,58,43,43,.north,1,1⟩,
  ⟨73,72,71,71,.west,0,5⟩,
  ⟨76,61,46,46,.north,1,1⟩,
  ⟨76,91,106,91,.south,1,1⟩,
  ⟨76,91,106,106,.south,2,16⟩,
  ⟨76,91,106,121,.south,2,2⟩,
  ⟨76,91,106,136,.south,16,16⟩,
  ⟨84,69,54,54,.north,2,8⟩,
  ⟨84,99,114,114,.south,0,10⟩,
  ⟨91,76,61,61,.north,1,1⟩,
  ⟨91,106,121,121,.south,1,1⟩,
  ⟨98,99,100,100,.east,2,10⟩,
  ⟨98,113,128,128,.south,0,12⟩,
  ⟨99,84,69,69,.north,2,9⟩,
  ⟨99,100,101,101,.east,2,9⟩,
  ⟨99,114,129,129,.south,0,11⟩,
  ⟨100,101,102,102,.east,2,8⟩,
  ⟨100,115,130,130,.south,0,10⟩,
  ⟨100,99,98,98,.west,10,10⟩,
  ⟨101,102,103,103,.east,7,7⟩,
  ⟨101,116,131,131,.south,0,9⟩,
  ⟨101,100,99,99,.west,0,9⟩,
  ⟨102,117,132,132,.south,0,8⟩,
  ⟨102,101,100,100,.west,0,8⟩,
  ⟨103,118,133,133,.south,1,1⟩,
  ⟨103,102,101,101,.west,0,7⟩,
  ⟨106,91,76,76,.north,1,1⟩,
  ⟨106,121,136,136,.south,15,15⟩,
  ⟨113,114,115,115,.east,2,11⟩,
  ⟨113,128,143,143,.south,13,13⟩,
  ⟨114,99,84,84,.north,2,10⟩,
  ⟨114,115,116,116,.east,2,10⟩,
  ⟨114,129,144,144,.south,12,12⟩,
  ⟨115,116,117,117,.east,2,9⟩,
  ⟨115,130,145,145,.south,11,11⟩,
  ⟨115,114,113,113,.west,0,11⟩,
  ⟨116,117,118,118,.east,8,8⟩,
  ⟨116,131,146,146,.south,10,10⟩,
  ⟨116,115,114,114,.west,0,10⟩,
  ⟨117,132,147,147,.south,9,9⟩,
  ⟨117,116,115,115,.west,0,9⟩,
  ⟨118,133,148,148,.south,1,1⟩,
  ⟨118,117,116,116,.west,0,8⟩,
  ⟨121,106,91,91,.north,0,0⟩,
  ⟨121,122,123,123,.east,1,1⟩,
  ⟨122,123,124,124,.east,1,1⟩,
  ⟨123,124,125,125,.east,1,1⟩,
  ⟨123,122,121,121,.west,1,1⟩,
  ⟨124,125,126,125,.east,1,1⟩,
  ⟨124,125,126,126,.east,2,15⟩,
  ⟨124,125,126,127,.east,2,15⟩,
  ⟨124,125,126,128,.east,3,15⟩,
  ⟨124,125,126,129,.east,4,15⟩,
  ⟨124,125,126,130,.east,5,15⟩,
  ⟨124,125,126,131,.east,6,15⟩,
  ⟨124,125,126,132,.east,7,15⟩,
  ⟨124,125,126,133,.east,15,15⟩,
  ⟨124,123,122,122,.west,1,1⟩,
  ⟨125,126,127,127,.east,1,14⟩,
  ⟨125,124,123,123,.west,1,1⟩,
  ⟨126,127,128,128,.east,2,14⟩,
  ⟨126,125,124,124,.west,1,1⟩,
  ⟨127,128,129,129,.east,2,13⟩,
  ⟨127,126,125,125,.west,0,0⟩,
  ⟨128,113,98,98,.north,12,12⟩,
  ⟨128,129,130,130,.east,2,12⟩,
  ⟨128,127,126,127,.west,1,14⟩,
  ⟨128,127,126,126,.west,1,14⟩,
  ⟨128,127,126,125,.west,0,0⟩,
  ⟨128,127,126,124,.west,0,0⟩,
  ⟨128,127,126,123,.west,0,0⟩,
  ⟨128,127,126,122,.west,0,0⟩,
  ⟨128,127,126,121,.west,0,0⟩,
  ⟨129,114,99,99,.north,2,11⟩,
  ⟨129,130,131,131,.east,2,11⟩,
  ⟨129,128,127,127,.west,0,13⟩,
  ⟨130,115,100,100,.north,2,10⟩,
  ⟨130,131,132,132,.east,2,10⟩,
  ⟨130,129,128,128,.west,0,12⟩,
  ⟨131,116,101,101,.north,2,9⟩,
  ⟨131,132,133,133,.east,9,9⟩,
  ⟨131,130,129,129,.west,0,11⟩,
  ⟨132,117,102,102,.north,2,8⟩,
  ⟨132,131,130,130,.west,0,10⟩,
  ⟨133,118,103,103,.north,1,1⟩,
  ⟨133,132,131,131,.west,0,9⟩,
  ⟨136,121,106,121,.north,1,1⟩,
  ⟨136,121,106,106,.north,1,15⟩,
  ⟨136,121,106,91,.north,0,0⟩,
  ⟨136,121,106,76,.north,0,0⟩,
  ⟨136,121,106,61,.north,0,0⟩,
  ⟨136,121,106,46,.north,0,0⟩,
  ⟨136,121,106,31,.north,0,0⟩,
  ⟨136,121,106,16,.north,15,15⟩,
  ⟨143,128,113,113,.north,2,13⟩,
  ⟨143,144,145,145,.east,1,1⟩,
  ⟨144,129,114,114,.north,2,12⟩,
  ⟨144,145,146,146,.east,1,1⟩,
  ⟨145,130,115,115,.north,2,11⟩,
  ⟨145,146,147,147,.east,1,1⟩,
  ⟨145,144,143,143,.west,1,1⟩,
  ⟨146,131,116,116,.north,2,10⟩,
  ⟨146,147,148,148,.east,1,1⟩,
  ⟨146,145,144,144,.west,1,1⟩,
  ⟨147,132,117,117,.north,2,9⟩,
  ⟨147,146,145,145,.west,1,1⟩,
  ⟨148,133,118,118,.north,1,1⟩,
  ⟨148,147,146,146,.west,1,1⟩]


def rowFacts (edge : Edge) : Bool := decide (
  advance soko4_2.board edge.player edge.direction = some edge.source ∧
  advance soko4_2.board edge.source edge.direction = some edge.first ∧
  edge.moveSlack = 1 + Generated.soko4_2Potential.boulder edge.landing - Generated.soko4_2Potential.boulder edge.source ∧
  edge.consumeSlack = 1 - Generated.soko4_2Potential.boulder edge.source - Generated.soko4_2Potential.hole edge.landing)

def checkedDirs : List Dir := [.north,.east,.south,.west,.northEast,.southEast,.southWest,.northWest]

theorem checkedDirs_complete (direction : Dir) : direction ∈ checkedDirs := by
  cases direction <;> simp [checkedDirs]

def computedEdge (player source : Cell) (direction : Dir) (landing : Cell) : Edge :=
  ⟨player, source, (advance soko4_2.board source direction).getD 0, landing, direction,
    1 + Generated.soko4_2Potential.boulder landing - Generated.soko4_2Potential.boulder source,
    1 - Generated.soko4_2Potential.boulder source - Generated.soko4_2Potential.hole landing⟩

def computedEdges : List Edge := soko4_2.board.floor.flatMap fun player => checkedDirs.flatMap fun direction =>
  match advance soko4_2.board player direction with
  | none => []
  | some source =>
    if !soko4_2.board.floor.contains source then []
    else (pushTargets soko4_2.board source direction).map (computedEdge player source direction)

def rowCheck (pattern : Nine) (edge : Edge) : Bool :=
  if known pattern edge.player || known pattern edge.first ||
      (known pattern edge.landing && decide (edge.landing ≠ edge.source)) then true
  else decide (bonus pattern ≤ edge.moveSlack + bonus (insert (erase pattern edge.source) edge.landing)) &&
    decide (bonus pattern ≤ edge.consumeSlack + bonus (erase pattern edge.source))

def allPatterns : List Nine := [false,true].flatMap fun a => [false,true].flatMap fun b =>
  [false,true].flatMap fun c => [false,true].flatMap fun d => [false,true].flatMap fun e =>
  [false,true].flatMap fun f => [false,true].flatMap fun g => [false,true].flatMap fun h =>
  [false,true].flatMap fun i => [⟨a,b,c,d,e,f,g,h,i⟩]

def goalCheck (pattern : Nine) : Bool := decide (
  bonus pattern ≤ weightSum debt (occupied pattern) + max 0 (Int.ofNat (occupied pattern).length - 2))

end NetHack.Sokoban.PatternCertificate
