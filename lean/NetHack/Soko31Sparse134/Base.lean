/- A proposed ONE-bit correction of the already proved full scalar133.
All finite local classifier rows and the original-Model bridge remain
obligations. This file alone asserts no new numerical lower bound. -/
import NetHack.Soko31Hero133.Verified
import NetHack.Sokoban.HeroPhasePotential.Strict
import NetHack.Sokoban.HeroPhasePotential.SmallPattern
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Sparse134
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf nextPhase afterBoxes)
abbrev phases := NetHack.Soko31Hero133.phases
def cert := NetHack.Soko31Hero133.certificate NetHack.Soko31Hero133.all_walk_rows
  NetHack.Soko31Hero133.all_push_rows NetHack.Soko31Hero133.all_advance_rows
abbrev weight := NetHack.Soko31Hero133.weight
abbrev holeWeight := NetHack.Soko31Hero133.holeWeight
def support : List Cell := [177,206,207]
def known (mask : Nat) (cell : Cell) : Bool :=
  if cell = 177 then mask.testBit 0 else
    if cell = 206 then mask.testBit 1 else
      if cell = 207 then mask.testBit 2 else false
def bonus (phase : Nat) (hero : Cell) (p : Pattern) : Nat :=
  if phase < 15 ∧ p 177 = true ∧ (p 206 = true ∨ (p 207 = true ∧ hero ≠ 178)) then 1 else 0

def Pay (phase : Nat) (hero : Cell) (p : Pattern) : Outcome → Prop
  | .walk _ => False
  | .push source (.stay landing) => weight phase hero source ≤ weight phase source landing
  | .push source (.fill hole) =>
      phase = 14 ∧ soko3_1.initial.holes.drop phase = [hole] ∧
      weight phase hero source + holeWeight hole ≤ 1 ∧
      ((p 206 = true ∧ 206 ≠ source ∧ weight phase hero 206 ≤ -1) ∨
       (p 207 = true ∧ 207 ≠ source ∧ weight phase hero 207 ≤ -1))
instance (phase : Nat) (hero : Cell) (p : Pattern) (outcome : Outcome) :
    Decidable (Pay phase hero p outcome) := by cases outcome with
  | walk _ => unfold Pay; infer_instance
  | push _ result => cases result <;> unfold Pay <;> infer_instance
def Result (phase : Nat) (hero : Cell) (p : Pattern) (outcome : Outcome) : Prop :=
  bonus phase hero p ≤ bonus (nextPhase phase outcome) (nextHero outcome) (afterBoxes p outcome) ∨
    Pay phase hero p outcome
instance (phase : Nat) (hero : Cell) (p : Pattern) (outcome : Outcome) :
    Decidable (Result phase hero p outcome) := by unfold Result; infer_instance

def WalkAllowed (phase : Nat) (hero target : Cell) (mask : Nat) (direction : Dir) : Prop :=
  hero ∈ soko3_1.board.floor ∧ hero ∉ soko3_1.board.doors ∧
  hero ∉ soko3_1.initial.holes.drop phase ∧ known mask hero = false ∧
  target ∈ soko3_1.board.floor ∧ target ∉ soko3_1.board.doors ∧
  target ∉ soko3_1.initial.holes.drop phase ∧ known mask target = false ∧
  corner soko3_1.board (known mask) hero direction = false
instance (phase : Nat) (hero target : Cell) (mask : Nat) (direction : Dir) :
    Decidable (WalkAllowed phase hero target mask direction) := by unfold WalkAllowed; infer_instance
def EndpointAllowed (mask source : Nat) : Ending → Prop
  | .stay landing => known mask landing = true → landing = source
  | .fill _ => True
instance (mask source : Nat) (result : Ending) : Decidable (EndpointAllowed mask source result) := by
  cases result <;> unfold EndpointAllowed <;> infer_instance
def PushAllowed (phase : Nat) (hero source : Cell) (mask : Nat)
    (direction : Dir) (result : Ending) : Prop :=
  hero ∈ soko3_1.board.floor ∧ hero ∉ soko3_1.board.doors ∧
  hero ∉ soko3_1.initial.holes.drop phase ∧ known mask hero = false ∧
  source ∈ phases.crates phase ∧ source ∈ soko3_1.board.floor ∧ source ∉ soko3_1.board.doors ∧
  (source ∈ support → known mask source = true) ∧
  corner soko3_1.board (known mask) hero direction = false ∧ EndpointAllowed mask source result
instance (phase : Nat) (hero source : Cell) (mask : Nat) (direction : Dir) (result : Ending) :
    Decidable (PushAllowed phase hero source mask direction result) := by unfold PushAllowed; infer_instance

def walkCheck (phase : Nat) (hero : Cell) (mask : Nat) (direction : Dir) : Bool :=
  match advance soko3_1.board hero direction with
  | none => true
  | some target => if WalkAllowed phase hero target mask direction then
      decide (Result phase hero (known mask) (.walk target)) else true
def pushCheck (phase : Nat) (hero : Cell) (mask : Nat) (direction : Dir) : Bool :=
  match advance soko3_1.board hero direction with
  | none => true
  | some source =>
      match pushOracle soko3_1.board HazardPhases.emptyBoxes
          (project (soko3_1.initial.holes.drop phase)) source direction with
      | none => true
      | some result => if PushAllowed phase hero source mask direction result then
          decide (Result phase hero (known mask) (.push source result)) else true
def check (phase : Nat) : Bool :=
  (phases.heroes phase).all fun hero => (List.range 8).all fun mask =>
    allDirs.all fun direction => walkCheck phase hero mask direction && pushCheck phase hero mask direction
end NetHack.Soko31Sparse134
