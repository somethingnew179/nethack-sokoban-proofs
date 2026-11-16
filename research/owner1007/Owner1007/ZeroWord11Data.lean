import Owner1007.TokenAccounting
import NetHack.Soko11Hero315.Reader
import NetHack.Sokoban.Geometry

namespace Owner1007.ZeroWord11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.PatternCorrection

def weight := NetHack.Soko11Hero315.weight 0
def singleSlack (hero box : Cell) : Outcome → Int
  | .walk target => weight target box - weight hero box
  | .push _ (.stay landing) => 1 + weight box landing - weight hero box
  | .push _ (.fill hole) => 1 - NetHack.Soko11Hero315.holeWeight hole - weight hero box

def H : List Cell := NetHack.SokobanLinearPhases.Map11.heroesRegion0
def upper : List Cell := H.filter fun c => decide (c < 164)
def upperTwo : List Cell := H.filter fun c => decide (c < 239)
def lowerTwo : List Cell := H.filter fun c => decide (183 ≤ c)
def lowerThree : List Cell := H.filter fun c => decide (262 ≤ c)
def belowEntry : List Cell := H.filter fun c => decide (106 ≤ c)
def remove (cells : List Cell) (box : Cell) : List Cell := cells.filter fun c => !(decide (c = box))
def cells : List Cell :=
  [137,138,164,190,216,215,214,213,239,265,291,265,239,213,187,188,189,190,164,138,
   112,111,85,59,139,191,193,192]
def cell (i : Nat) : Cell := cells[i]?.getD 0

def region (i : Nat) : List Cell :=
  match i with
  | 0 => remove H 137
  | 1 => remove upper 138
  | 2 => upper
  | 3 => upper ++ [164]
  | 4 => remove H 216
  | 5 => remove H 215
  | 6 => remove H 214
  | 7 => remove upperTwo 213
  | 8 => upperTwo
  | 9 => upperTwo ++ [239]
  | 10 => remove H 291
  | 11 => remove lowerThree 265
  | 12 => lowerThree
  | 13 => lowerThree ++ [239]
  | 14 => remove H 187
  | 15 => remove H 188
  | 16 => remove H 189
  | 17 => remove lowerTwo 190
  | 18 => lowerTwo
  | 19 => lowerTwo ++ [164]
  | 20 => remove H 112
  | 21 => remove belowEntry 111
  | 22 => belowEntry
  | 23 => H.filter fun c => decide (85 ≤ c)
  | 24 => remove H 139
  | 25 => remove H 191
  | 26 => remove H 193
  | 27 => remove H 192
  | _ => []

def successor (i : Nat) : Nat :=
  if i = 24 then 1 else if i = 25 then 17 else if i = 26 then 27 else if i = 27 then 25 else i+1

def Next (i : Nat) : Outcome → Prop
  | .walk target => target ∈ region i
  | .push source (.stay landing) =>
      source = cell i ∧ i ≠ 23 ∧ landing = cell (successor i) ∧ source ∈ region (successor i)
  | .push source (.fill hole) => source = cell i ∧ i = 23 ∧ hole = 33
instance (i : Nat) (o : Outcome) : Decidable (Next i o) := by
  cases o with
  | walk target => unfold Next; infer_instance
  | push source result => cases result <;> unfold Next <;> infer_instance

def walkNodeCheck (i : Nat) : Bool :=
  (region i).all fun hero => allDirs.all fun dir =>
    match advance soko1_1.board hero dir with
    | none => true
    | some target => decide ((target ∈ soko1_1.board.floor ∧ target ∉ soko1_1.board.doors ∧
        target ≠ cell i ∧ target ∉ soko1_1.initial.holes ∧
        corner soko1_1.board (project [cell i]) hero dir = false) → target ∈ region i)

def pushNodeCheck (i : Nat) : Bool :=
  allDirs.all fun dir =>
    match advance soko1_1.board (cell i) dir.opposite with
    | none => true
    | some hero =>
      if hero ∈ region i then
        match pushOracle soko1_1.board HazardPhases.emptyBoxes (project soko1_1.initial.holes) (cell i) dir with
        | none => true
        | some e => decide (singleSlack hero (cell i) (.push (cell i) e) ≠ 0 ∨ Next i (.push (cell i) e))
      else true

def nodeCheck (i : Nat) : Bool := walkNodeCheck i && pushNodeCheck i
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem H_walk (hero target : Cell) (dir : Dir) (inside : hero ∈ H)
    (adjacent : advance soko1_1.board hero dir = some target)
    (floor : target ∈ soko1_1.board.floor) (notHole : target ∉ soko1_1.initial.holes) :
    target ∈ H := by
  exact NetHack.SokobanLinearPhases.Map11.certificate.walk 0 (by decide) hero inside dir target adjacent floor notHole

theorem full_remove_walk (box hero target : Cell) (dir : Dir)
    (inside : hero ∈ remove H box) (adjacent : advance soko1_1.board hero dir = some target)
    (floor : target ∈ soko1_1.board.floor) (different : target ≠ box)
    (notHole : target ∉ soko1_1.initial.holes) : target ∈ remove H box := by
  have heroH := (List.mem_filter.mp inside).1
  have targetH := H_walk hero target dir heroH adjacent floor notHole
  exact List.mem_filter.mpr ⟨targetH, by simp [different]⟩

theorem walk_of_closed (i : Nat)
    (closed : ∀ hero ∈ region i, ∀ dir target,
      advance soko1_1.board hero dir = some target →
      target ∈ soko1_1.board.floor → target ∉ soko1_1.board.doors →
      target ≠ cell i → target ∉ soko1_1.initial.holes →
      corner soko1_1.board (project [cell i]) hero dir = false → target ∈ region i) :
    walkNodeCheck i = true := by
  unfold walkNodeCheck
  apply List.all_eq_true.mpr
  intro hero inside
  apply List.all_eq_true.mpr
  intro dir _
  cases adjacent : advance soko1_1.board hero dir with
  | none => rfl
  | some target =>
    apply decide_eq_true
    intro premises
    exact closed hero inside dir target adjacent premises.1 premises.2.1
      premises.2.2.1 premises.2.2.2.1 premises.2.2.2.2

#print axioms H_walk
#print axioms walk_of_closed
end Owner1007.ZeroWord11
