/- Finite scalar certificates for HeroPhasePotential.Core. Every actual walk
and collision-free rolled push is covered. Numeric comparisons short-circuit
geometry only when the desired inequality is already true. No native proof
reflection, unchecked region/assignment output, or new axiom is used. -/
import NetHack.Sokoban.HeroPhasePotential.Core

namespace NetHack.Sokoban.HeroPhasePotential
open HazardPattern

def WalkAllowed (board : Board) (holes : List Cell) (hero box target : Cell)
    (direction : Dir) : Prop :=
  hero ∈ board.floor ∧ hero ∉ board.doors ∧ hero ∉ holes ∧ hero ≠ box ∧
  target ∈ board.floor ∧ target ∉ board.doors ∧ target ∉ holes ∧ target ≠ box ∧
  corner board (PatternCorrection.project [box]) hero direction = false

instance (board : Board) (holes : List Cell) (hero box target : Cell) (direction : Dir) :
    Decidable (WalkAllowed board holes hero box target direction) := by
  unfold WalkAllowed
  infer_instance

def walkCheck (board : Board) (holes : List Cell) (box : Cell) (row : Cell → Int)
    (hero : Cell) (direction : Dir) : Bool :=
  match advance board hero direction with
  | none => true
  | some target => decide (row hero ≤ row target) ||
      decide (¬WalkAllowed board holes hero box target direction)

def walkRow (board : Board) (holes heroes : List Cell) (box : Cell)
    (row : Cell → Int) : Bool :=
  heroes.all fun hero => allDirs.all (walkCheck board holes box row hero)

theorem walkRow_sound (board : Board) (holes heroes : List Cell) (box : Cell)
    (row : Cell → Int) (checked : walkRow board holes heroes box row = true)
    (hero : Cell) (member : hero ∈ heroes) (direction : Dir) (target : Cell)
    (adjacent : advance board hero direction = some target)
    (allowed : WalkAllowed board holes hero box target direction) : row hero ≤ row target := by
  have selected := List.all_eq_true.mp
    (List.all_eq_true.mp checked hero member) direction (Geometry.all_directions direction)
  simp only [walkCheck, adjacent] at selected
  rcases Bool.or_eq_true_iff.mp selected with numeric | forbidden
  · exact of_decide_eq_true numeric
  · exact False.elim ((of_decide_eq_true forbidden) allowed)

def PushStanding (board : Board) (holes heroes : List Cell) (hero source : Cell) : Prop :=
  hero ∈ heroes ∧ hero ∈ board.floor ∧ hero ∉ board.doors ∧ hero ∉ holes ∧ hero ≠ source ∧
  source ∈ board.floor ∧ source ∉ board.doors

instance (board : Board) (holes heroes : List Cell) (hero source : Cell) :
    Decidable (PushStanding board holes heroes hero source) := by
  unfold PushStanding
  infer_instance

def pushCheck (board : Board) (holes heroes : List Cell) (source : Cell)
    (before after holeWeight : Cell → Int) (direction : Dir) : Bool :=
  match advance board source direction.opposite with
  | none => true
  | some hero =>
    if PushStanding board holes heroes hero source then
      match pushOracle board HazardPhases.emptyBoxes (PatternCorrection.project holes) source direction with
      | none => true
      | some (.stay landing) => decide (before hero ≤ 1 + after landing)
      | some (.fill hole) => decide (before hero + holeWeight hole ≤ 1)
    else true

def pushRow (board : Board) (holes heroes : List Cell) (source : Cell)
    (before after holeWeight : Cell → Int) : Bool :=
  allDirs.all (pushCheck board holes heroes source before after holeWeight)

theorem pushRow_sound (board : Board) (reverse : Geometry.reverseCheck board = true)
    (holes heroes : List Cell) (source : Cell) (before after holeWeight : Cell → Int)
    (checked : pushRow board holes heroes source before after holeWeight = true)
    (hero : Cell) (standing : PushStanding board holes heroes hero source)
    (direction : Dir) (result : Ending) (adjacent : advance board hero direction = some source)
    (oracle : pushOracle board HazardPhases.emptyBoxes (PatternCorrection.project holes)
      source direction = some result) :
    match result with
    | .stay landing => before hero ≤ 1 + after landing
    | .fill hole => before hero + holeWeight hole ≤ 1 := by
  have support := Geometry.reverseCheck_sound board reverse hero standing.2.1 direction source adjacent
  have selected := List.all_eq_true.mp checked direction (Geometry.all_directions direction)
  simp only [pushCheck, support, if_pos standing, oracle] at selected
  cases result with
  | stay landing => exact of_decide_eq_true selected
  | fill hole => exact of_decide_eq_true selected

def AdvanceAllowed (board : Board) (holes : List Cell) (hero box : Cell) : Prop :=
  hero ∉ board.doors ∧ hero ∉ holes ∧ hero ≠ box

instance (board : Board) (holes : List Cell) (hero box : Cell) :
    Decidable (AdvanceAllowed board holes hero box) := by
  unfold AdvanceAllowed
  infer_instance

def advanceRow (board : Board) (holes : List Cell) (box : Cell)
    (before after : Cell → Int) : Bool :=
  board.floor.all fun hero => decide (before hero ≤ after hero) ||
    decide (¬AdvanceAllowed board holes hero box)

theorem advanceRow_sound (board : Board) (holes : List Cell) (box : Cell)
    (before after : Cell → Int) (checked : advanceRow board holes box before after = true)
    (hero : Cell) (floor : hero ∈ board.floor) (allowed : AdvanceAllowed board holes hero box) :
    before hero ≤ after hero := by
  have selected := List.all_eq_true.mp checked hero floor
  rcases Bool.or_eq_true_iff.mp selected with numeric | forbidden
  · exact of_decide_eq_true numeric
  · exact False.elim ((of_decide_eq_true forbidden) allowed)

def disjointRow (holes crates : List Cell) : Bool :=
  crates.all fun box => !holes.contains box

theorem disjointRow_sound (holes crates : List Cell) (checked : disjointRow holes crates = true) :
    ∀ box ∈ crates, box ∉ holes := by
  intro box member
  have selected := List.all_eq_true.mp checked box member
  have absent : holes.contains box = false := by simpa only [Bool.not_eq_true'] using selected
  intro present
  have yes : holes.contains box = true := List.contains_iff_mem.mpr present
  have impossible := yes.symm.trans absent
  cases impossible

/-- All fields remain proof obligations on exact original regions, directions
and weighted values. In particular this function does not trust a PDB generator. -/
def ofRows (board : Board) (original : List Cell) (phases : HazardPhases.Certificate board original)
    (weight : Nat → Cell → Cell → Int) (holeWeight : Cell → Int)
    (reverse : Geometry.reverseCheck board = true)
    (disjoint : ∀ phase, phase ≤ original.length →
      disjointRow (original.drop phase) (phases.crates phase) = true)
    (walked : ∀ phase, phase < original.length → ∀ box ∈ phases.crates phase,
      walkRow board (original.drop phase) (phases.heroes phase) box (fun hero => weight phase hero box) = true)
    (pushed : ∀ phase, phase < original.length → ∀ source ∈ phases.crates phase,
      pushRow board (original.drop phase) (phases.heroes phase) source
        (fun hero => weight phase hero source) (fun landing => weight phase source landing) holeWeight = true)
    (advanced : ∀ phase, phase < original.length → ∀ box ∈ phases.crates phase,
      advanceRow board (original.drop phase) box
        (fun hero => weight phase hero box) (fun hero => weight (phase+1) hero box) = true)
    (terminal : ∀ hero box, weight original.length hero box ≤ 0) :
    Certificate board original phases where
  weight := weight
  holeWeight := holeWeight
  crate_disjoint := fun phase bound => disjointRow_sound _ _ (disjoint phase bound)
  walk := by
    intro phase active hero heroMember box boxMember direction target hf hd hh hb adjacent tf td th tb corner
    exact walkRow_sound board _ _ box _ (walked phase active box boxMember) hero heroMember
      direction target adjacent ⟨hf,hd,hh,hb,tf,td,th,tb,corner⟩
  push := by
    intro phase active hero heroMember source sourceMember direction result hf hd hh hb sf sd adjacent oracle
    cases result with
    | stay landing =>
      exact pushRow_sound board reverse _ _ source _ _ _ (pushed phase active source sourceMember)
        hero ⟨heroMember,hf,hd,hh,hb,sf,sd⟩ direction (.stay landing) adjacent oracle
    | fill hole =>
      exact pushRow_sound board reverse _ _ source _ _ _ (pushed phase active source sourceMember)
        hero ⟨heroMember,hf,hd,hh,hb,sf,sd⟩ direction (.fill hole) adjacent oracle
  advancePhase := by
    intro phase active hero floor door hole box member next different
    exact advanceRow_sound board _ box _ _ (advanced phase active box member)
      hero floor ⟨door,hole,different⟩
  terminal := terminal

end NetHack.Sokoban.HeroPhasePotential
