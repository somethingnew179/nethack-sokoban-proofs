/- The actual RLT/consumption transfer for interior phases, separately from
the already checked data equalities. The first open hole changes; its label
is normalized only in the oracle outcome, never in the Model or Trace. -/
import NetHack.Soko11PairCandidate321.InteriorAll
import NetHack.Sokoban.GhostHoleTransfer
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.GhostHoleTransfer
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def simpleGeometry (phase source : Nat) (direction : Dir) : Bool :=
  if source = 33 ∧ direction = .east then true
  else if direction.diagonal then true
  else match advance soko1_1.board source direction with
    | none => true
    | some destination => decide (destination ∉ soko1_1.initial.holes.drop phase ∧
        destination ∉ soko1_1.initial.holes.drop 14 ∧ destination ∉ soko1_1.board.rollingTraps)

def geometryAt (phase : Nat) : Bool :=
  decide (NetHack.Soko11Hero315.phases.crates phase = NetHack.Soko11Hero315.phases.crates 14 ∧
    NetHack.Soko11Hero315.phases.heroes phase ⊆ NetHack.Soko11Hero315.phases.heroes 14 ∧
    soko1_1.initial.holes.drop 14 ⊆ soko1_1.initial.holes.drop phase) &&
  (NetHack.Soko11Hero315.phases.crates 14).all (fun source =>
    allDirs.all (simpleGeometry phase source)) &&
  decide (pushOracle soko1_1.board (project (NetHack.Soko11Hero315.phases.crates 14))
    (project (soko1_1.initial.holes.drop phase)) 33 .east = some (.fill (phase+34)))
def interiorGeometryCheck : Bool :=
  (List.range 16).all fun phase => if 1 ≤ phase ∧ phase ≤ 14 then geometryAt phase else true
theorem checked_interior_geometry : interiorGeometryCheck = true := by decide +kernel

theorem geometry_at (phase : Nat) (lower : 1 ≤ phase) (upper : phase ≤ 14) : geometryAt phase = true := by
  have h := List.all_eq_true.mp checked_interior_geometry phase (List.mem_range.mpr (by omega))
  simpa only [if_pos (And.intro lower upper)] using h

theorem interior_support (phase : Nat) (lower : 1 ≤ phase) (upper : phase ≤ 14) :
    NetHack.Soko11Hero315.phases.crates phase = NetHack.Soko11Hero315.phases.crates 14 ∧
    NetHack.Soko11Hero315.phases.heroes phase ⊆ NetHack.Soko11Hero315.phases.heroes 14 ∧
    soko1_1.initial.holes.drop 14 ⊆ soko1_1.initial.holes.drop phase := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (geometry_at phase lower upper)).1).1
  exact of_decide_eq_true h

theorem interior_push_transfer (phase : Nat) (lower : 1 ≤ phase) (upper : phase ≤ 14)
    (group : List Cell) (inside : group ⊆ NetHack.Soko11Hero315.phases.crates phase)
    (source : Cell) (present : source ∈ group) (direction : Dir) (result : Ending)
    (oracle : pushOracle soko1_1.board (project group)
      (project (soko1_1.initial.holes.drop phase)) source direction = some result) :
    pushOracle soko1_1.board (project group) (project (soko1_1.initial.holes.drop 14)) source direction =
      some (canonicalEnding 48 result) := by
  have geometry := interior_support phase lower upper
  have contained : group ⊆ NetHack.Soko11Hero315.phases.crates 14 := by rw [←geometry.1]; exact inside
  by_cases special : source = 33 ∧ direction = .east
  · rcases special with ⟨rfl,rfl⟩
    have original := of_decide_eq_true (Bool.and_eq_true_iff.mp (geometry_at phase lower upper)).2
    have current := GhostProjection.push_subset_covers soko1_1.board (project group)
      (project (NetHack.Soko11Hero315.phases.crates 14)) (project (soko1_1.initial.holes.drop phase))
      (GhostProjection.project_subset _ _ contained) 33 .east (.fill (phase+34)) original
    have label : result = .fill (phase+34) := Option.some.inj (oracle.symm.trans current)
    have reference := of_decide_eq_true (Bool.and_eq_true_iff.mp (geometry_at 14 (by omega) (by omega))).2
    have after := GhostProjection.push_subset_covers soko1_1.board (project group)
      (project (NetHack.Soko11Hero315.phases.crates 14)) (project (soko1_1.initial.holes.drop 14))
      (GhostProjection.project_subset _ _ contained) 33 .east (.fill 48) reference
    rw [label]
    exact after
  · cases diagonal : direction.diagonal with
    | true => simp [pushOracle,diagonal] at oracle
    | false =>
      have all := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (geometry_at phase lower upper)).1).2
      have numeric := List.all_eq_true.mp (List.all_eq_true.mp all source (contained present))
        direction (Geometry.all_directions direction)
      have simple : ∀ destination, advance soko1_1.board source direction = some destination →
          project (soko1_1.initial.holes.drop phase) destination = false ∧
          project (soko1_1.initial.holes.drop 14) destination = false ∧
          soko1_1.board.rollingTraps.contains destination = false := by
        intro destination adjacent
        simp only [simpleGeometry,if_neg special,diagonal,Bool.false_eq_true,↓reduceIte,adjacent] at numeric
        rcases of_decide_eq_true numeric with ⟨a,b,c⟩
        exact ⟨by simp [project,a],by simp [project,b],by simp [c]⟩
      have same := push_no_roll_equal soko1_1.board (project group)
        (project (soko1_1.initial.holes.drop phase)) (project (soko1_1.initial.holes.drop 14)) source direction simple
      have noFill : ∀ cell, result ≠ .fill cell := by
        intro cell
        intro eq
        subst result
        have empty := HazardPhases.push_empty_covers soko1_1.board (project group)
          (project (soko1_1.initial.holes.drop phase)) source direction (.fill cell) oracle
        -- For a non-rolling push the same destination tests preclude a fill.
        cases behind : advance soko1_1.board source direction.opposite with
        | none => simp [pushOracle,diagonal,behind] at empty
        | some support =>
          cases destination : advance soko1_1.board source direction with
          | none => simp [pushOracle,diagonal,behind,destination] at empty
          | some target =>
            rcases simple target destination with ⟨a,b,c⟩
            have notRolling : target ∉ soko1_1.board.rollingTraps := by simpa using c
            simp [pushOracle,diagonal,behind,destination,a,notRolling,HazardPhases.emptyBoxes] at empty
      cases result with
      | fill hole => exact False.elim (noFill hole rfl)
      | stay landing => simpa only [canonicalEnding] using same.symm.trans oracle

theorem interior_oracle_transfer (phase : Nat) (lower : 1 ≤ phase) (upper : phase ≤ 14)
    (hero : Cell) (group : List Cell) (inside : group ⊆ NetHack.Soko11Hero315.phases.crates phase)
    (clear : hero ∉ soko1_1.initial.holes.drop phase) (direction : Dir) (outcome : Outcome)
    (oracle : stepOracle soko1_1.board (project group)
      (project (soko1_1.initial.holes.drop phase)) hero direction = some outcome) :
    stepOracle soko1_1.board (project group) (project (soko1_1.initial.holes.drop 14)) hero direction =
      some (canonicalOutcome 48 outcome) := by
  have geometry := interior_support phase lower upper
  have heroFirst : project (soko1_1.initial.holes.drop phase) hero = false := by simp [project,clear]
  have heroSecond : project (soko1_1.initial.holes.drop 14) hero = false := by
    have absent : hero ∉ soko1_1.initial.holes.drop 14 := fun h => clear (geometry.2.2 h)
    simp [project,absent]
  exact step_transfer soko1_1.board (project group) (project (soko1_1.initial.holes.drop phase))
    (project (soko1_1.initial.holes.drop 14)) 48 hero direction outcome heroFirst heroSecond
    (GhostProjection.project_subset _ _ geometry.2.2)
    (fun source present result checked => interior_push_transfer phase lower upper group inside source
      (List.contains_iff_mem.mp present) direction result checked) oracle

end NetHack.Soko11PairCandidate321
