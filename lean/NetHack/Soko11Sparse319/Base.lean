/- A proposed four-cell correction of the proved actor scalar315.
All finite local classifier rows and the original-Model bridge remain
obligations. This file alone asserts no new numerical lower bound. -/
import NetHack.Soko11Hero315.Verified
import NetHack.Sokoban.HeroPhasePotential.SparseCredit
import NetHack.Sokoban.HeroPhasePotential.SmallPattern
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Sparse319
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf nextPhase afterBoxes)
abbrev phases := NetHack.Soko11Hero315.phases
def cert := NetHack.Soko11Hero315.certificate NetHack.Soko11Hero315.all_walk_rows
  NetHack.Soko11Hero315.all_push_rows NetHack.Soko11Hero315.all_advance_rows
abbrev weight := NetHack.Soko11Hero315.weight
abbrev holeWeight := NetHack.Soko11Hero315.holeWeight
def support : List Cell := [185, 186, 211, 212]
def known (mask : Nat) (cell : Cell) : Bool :=
  if cell = 185 then mask.testBit 0 else
  if cell = 186 then mask.testBit 1 else
  if cell = 211 then mask.testBit 2 else
  if cell = 212 then mask.testBit 3 else
  false
def maskOf (p : Pattern) : Nat :=
  (if p 185 then 1 else 0) + (if p 186 then 2 else 0) + (if p 211 then 4 else 0) + (if p 212 then 8 else 0)
def word (hero : Cell) : Nat :=
  if ([212] : List Cell).contains hero then 0xc90c00 else
  if ([211] : List Cell).contains hero then 0xc00000c00 else
  if ([186] : List Cell).contains hero then 0x36010010000 else
  if ([185] : List Cell).contains hero then 0x186000000000 else
  if ([183, 184, 209, 210] : List Cell).contains hero then 0xdb6c00c00c00 else
  0xdb6d10c90c00
def bonus (phase hero : Nat) (p : Pattern) : Nat :=
  if phase < 16 then (word hero >>> (3 * maskOf p)) % 8 else 0
def selected (p : Pattern) : Outcome → List Cell
  | .walk _ => support.filter fun cell => p cell
  | .push source _ => support.filter fun cell => p cell && decide (cell ≠ source)
def Result (phase hero : Nat) (p : Pattern) (outcome : Outcome) : Prop :=
  bonus phase hero p ≤ bonus (nextPhase phase outcome) (nextHero outcome) (afterBoxes p outcome) ∨
    HeroPhasePotential.SparseCredit.localCondition cert phase hero (selected p outcome)
      (Int.ofNat (bonus phase hero p))
      (Int.ofNat (bonus (nextPhase phase outcome) (nextHero outcome) (afterBoxes p outcome))) outcome
instance (phase hero : Nat) (p : Pattern) (outcome : Outcome) : Decidable (Result phase hero p outcome) := by
  unfold Result; infer_instance
def WalkAllowed (phase : Nat) (hero target : Cell) (mask : Nat) (direction : Dir) : Prop :=
  hero ∈ soko1_1.board.floor ∧ hero ∉ soko1_1.board.doors ∧
  hero ∉ soko1_1.initial.holes.drop phase ∧ known mask hero = false ∧
  target ∈ soko1_1.board.floor ∧ target ∉ soko1_1.board.doors ∧
  target ∉ soko1_1.initial.holes.drop phase ∧ known mask target = false ∧
  corner soko1_1.board (known mask) hero direction = false
instance (phase : Nat) (hero target : Cell) (mask : Nat) (direction : Dir) :
    Decidable (WalkAllowed phase hero target mask direction) := by unfold WalkAllowed; infer_instance
def EndpointAllowed (mask source : Nat) : Ending → Prop
  | .stay landing => known mask landing = true → landing = source
  | .fill _ => True
instance (mask source : Nat) (result : Ending) : Decidable (EndpointAllowed mask source result) := by
  cases result <;> unfold EndpointAllowed <;> infer_instance
def PushAllowed (phase : Nat) (hero source : Cell) (mask : Nat)
    (direction : Dir) (result : Ending) : Prop :=
  hero ∈ soko1_1.board.floor ∧ hero ∉ soko1_1.board.doors ∧
  hero ∉ soko1_1.initial.holes.drop phase ∧ known mask hero = false ∧
  source ∈ phases.crates phase ∧ source ∈ soko1_1.board.floor ∧ source ∉ soko1_1.board.doors ∧
  (source ∈ support → known mask source = true) ∧
  corner soko1_1.board (known mask) hero direction = false ∧ EndpointAllowed mask source result
instance (phase : Nat) (hero source : Cell) (mask : Nat) (direction : Dir) (result : Ending) :
    Decidable (PushAllowed phase hero source mask direction result) := by unfold PushAllowed; infer_instance

def walkCheck (phase : Nat) (hero : Cell) (mask : Nat) (direction : Dir) : Bool :=
  match advance soko1_1.board hero direction with
  | none => true
  | some target => if WalkAllowed phase hero target mask direction then
      decide (Result phase hero (known mask) (.walk target)) else true
def pushCheck (phase : Nat) (hero : Cell) (mask : Nat) (direction : Dir) : Bool :=
  match advance soko1_1.board hero direction with
  | none => true
  | some source =>
      match pushOracle soko1_1.board HazardPhases.emptyBoxes
          (project (soko1_1.initial.holes.drop phase)) source direction with
      | none => true
      | some result => if PushAllowed phase hero source mask direction result then
          decide (Result phase hero (known mask) (.push source result)) else true
def check (phase : Nat) : Bool :=
  (phases.heroes phase).all fun hero => (List.range 16).all fun mask =>
    allDirs.all fun direction => walkCheck phase hero mask direction && pushCheck phase hero mask direction
end NetHack.Soko11Sparse319
