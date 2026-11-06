/- Composition of checked substitutions, physical cubes, and counted numeric
rows. This verifies certificate equations; covering Model/oracle transitions
and establishing each physical/count premise remain explicit obligations. -/
import NetHack.Sokoban.DecisionDAGCountedBounded
import NetHack.Sokoban.DecisionDAGTransform
import NetHack.Sokoban.PatternMass
namespace NetHack.Sokoban.CountedLocalCase
open DecisionDAG (Node Pattern eval)
open DecisionDAGTransform (Bindings Satisfies update)
open DecisionDAGCountedCompact (count count_split)

def eraseBindings : List Cell → Bindings → List Cell
  | cells, [] => cells
  | cells, binding :: tail =>
    eraseBindings (cells.filter (fun cell => decide (cell ≠ binding.1))) tail

def charge : List Cell → Bindings → Int
  | _, [] => 0
  | cells, binding :: tail =>
    (if binding.2 then Int.ofNat ((cells.filter (fun cell => decide (cell = binding.1))).length) else 0) +
      charge (cells.filter (fun cell => decide (cell ≠ binding.1))) tail

theorem erase_count (cells : List Cell) (bindings : Bindings) (p : Pattern)
    (satisfied : Satisfies bindings p) :
    count (eraseBindings cells bindings) p + charge cells bindings = count cells p := by
  induction bindings generalizing cells with
  | nil => simp [eraseBindings, charge]
  | cons binding tail ih =>
    have selected := satisfied binding (by simp)
    have rest : Satisfies tail p := fun entry member =>
      satisfied entry (List.mem_cons_of_mem binding member)
    have filtered := count_split cells p binding.1 binding.2 selected
    have next := ih (cells.filter (fun cell => decide (cell ≠ binding.1))) rest
    simp only [eraseBindings, charge]
    omega

theorem count_eq_mass (cells : List Cell) (p : Pattern) :
    count cells p = Int.ofNat (PatternMass.mass cells p) := by
  induction cells with
  | nil => rfl
  | cons cell tail ih =>
    cases selected : p cell <;> simp [count, PatternMass.mass, selected] at ih ⊢ <;> omega

theorem oracle_push_source (board : Board) (boxes holes : Pattern) (hero : Cell)
    (direction : Dir) (source : Cell) (result : HazardPattern.Ending)
    (checked : HazardPattern.stepOracle board boxes holes hero direction =
      some (.push source result)) : boxes source = true := by
  cases blocked : boxes hero || holes hero with
  | true => simp [HazardPattern.stepOracle, blocked] at checked
  | false =>
    cases adjacent : advance board hero direction with
    | none => simp [HazardPattern.stepOracle, blocked, adjacent] at checked
    | some target =>
      cases present : boxes target with
      | false =>
        cases hole : holes target <;>
          simp [HazardPattern.stepOracle, blocked, adjacent, present, hole] at checked
      | true =>
        cases pushed : HazardPattern.pushOracle board boxes holes target direction with
        | none => simp [HazardPattern.stepOracle, blocked, adjacent, present, pushed] at checked
        | some ending =>
          simp [HazardPattern.stepOracle, blocked, adjacent, present, pushed] at checked
          rw [← checked.2.1]
          exact present

structure System where
  read : Nat → Node
  support : List Cell
  updates : Nat → DecisionDAGTransform.UpdateRow
  updateCount : Nat
  updatesValid : ∀ index, index < updateCount →
    DecisionDAGTransform.UpdateHolds read (updates index).claim
  restrictions : Nat → DecisionDAGTransform.RestrictionRow
  restrictionCount : Nat
  restrictionsValid : ∀ index, index < restrictionCount →
    DecisionDAGTransform.RestrictionHolds read (restrictions index).claim
  numeric : Nat → DecisionDAGCountedBounded.Row
  numericCount : Nat
  numericValid : ∀ index, index < numericCount →
    DecisionDAGCountedCompact.Holds read (numeric index).claim

structure Frame where
  bindings : Bindings
  budget : Int
  changes : Bindings
  beforeBeta : Nat
  beforeBonus : Nat
  afterBeta : Nat
  afterBonus : Nat
  preBeta : Nat
  preBonus : Nat
  restrictionBeforeBeta : Nat
  restrictionBeforeBonus : Nat
  restrictionAfterBeta : Nat
  restrictionAfterBonus : Nat
  updateProofs : Option (Nat × Nat)
  numericProof : Nat
  slack : Int
  deriving DecidableEq, Repr

def updateGuard (sys : System) (frame : Frame) : Bool :=
  match frame.updateProofs with
  | none => decide (frame.changes = [] ∧ frame.preBeta = frame.afterBeta ∧ frame.preBonus = frame.afterBonus)
  | some (beta, bonus) => decide (beta < sys.updateCount ∧ bonus < sys.updateCount ∧
      (sys.updates beta).claim = ⟨frame.changes, frame.afterBeta, frame.preBeta⟩ ∧
      (sys.updates bonus).claim = ⟨frame.changes, frame.afterBonus, frame.preBonus⟩)

theorem updateGuard_sound (sys : System) (frame : Frame)
    (checked : updateGuard sys frame = true) (p : Pattern) :
    eval sys.read p frame.preBeta = eval sys.read (update p frame.changes) frame.afterBeta ∧
    eval sys.read p frame.preBonus = eval sys.read (update p frame.changes) frame.afterBonus := by
  cases proof : frame.updateProofs with
  | none =>
    have facts : frame.changes = [] ∧ frame.preBeta = frame.afterBeta ∧ frame.preBonus = frame.afterBonus := by
      simpa only [updateGuard, proof, decide_eq_true_eq] using checked
    simp only [facts.1, facts.2.1, facts.2.2]
    exact ⟨rfl, rfl⟩
  | some pair =>
    rcases pair with ⟨beta, bonus⟩
    have facts : beta < sys.updateCount ∧ bonus < sys.updateCount ∧
        (sys.updates beta).claim = ⟨frame.changes, frame.afterBeta, frame.preBeta⟩ ∧
        (sys.updates bonus).claim = ⟨frame.changes, frame.afterBonus, frame.preBonus⟩ := by
      simpa only [updateGuard, proof, decide_eq_true_eq] using checked
    have first := sys.updatesValid beta facts.1
    have second := sys.updatesValid bonus facts.2.1
    rw [facts.2.2.1] at first
    rw [facts.2.2.2] at second
    exact ⟨first p, second p⟩

def restrictionGuard (sys : System) (bindings : Bindings) (index original : Nat) : Bool :=
  decide (index < sys.restrictionCount ∧ (sys.restrictions index).claim.original = original ∧
    (sys.restrictions index).claim.bindings ⊆ bindings)

theorem restrictionGuard_sound (sys : System) (bindings : Bindings) (index original : Nat)
    (checked : restrictionGuard sys bindings index original = true)
    (p : Pattern) (satisfied : Satisfies bindings p) :
    eval sys.read p (sys.restrictions index).claim.output = eval sys.read p original := by
  have facts : index < sys.restrictionCount ∧ (sys.restrictions index).claim.original = original ∧
      (sys.restrictions index).claim.bindings ⊆ bindings := of_decide_eq_true checked
  have result := sys.restrictionsValid index facts.1 p
    (fun binding member => satisfied binding (facts.2.2 member))
  simpa only [facts.2.1] using result

def template (sys : System) (frame : Frame) : DecisionDAGCountedCompact.Claim :=
  ⟨[], eraseBindings sys.support frame.bindings, frame.budget - charge sys.support frame.bindings,
    (sys.restrictions frame.restrictionBeforeBeta).claim.output,
    (sys.restrictions frame.restrictionBeforeBonus).claim.output,
    (sys.restrictions frame.restrictionAfterBeta).claim.output,
    (sys.restrictions frame.restrictionAfterBonus).claim.output, frame.slack, true⟩

def check (sys : System) (frame : Frame) : Bool :=
  decide (updateGuard sys frame = true ∧
    restrictionGuard sys frame.bindings frame.restrictionBeforeBeta frame.beforeBeta = true ∧
    restrictionGuard sys frame.bindings frame.restrictionBeforeBonus frame.beforeBonus = true ∧
    restrictionGuard sys frame.bindings frame.restrictionAfterBeta frame.preBeta = true ∧
    restrictionGuard sys frame.bindings frame.restrictionAfterBonus frame.preBonus = true ∧
    frame.numericProof < sys.numericCount ∧
    (sys.numeric frame.numericProof).claim = (template sys frame).normalize)

def Holds (sys : System) (frame : Frame) : Prop :=
  ∀ p, Satisfies frame.bindings p → count sys.support p ≤ frame.budget →
    eval sys.read (update p frame.changes) frame.afterBonus < eval sys.read p frame.beforeBonus →
    eval sys.read p frame.beforeBeta + eval sys.read p frame.beforeBonus ≤ frame.slack +
      eval sys.read (update p frame.changes) frame.afterBeta +
      eval sys.read (update p frame.changes) frame.afterBonus

theorem checked_sound (sys : System) (frame : Frame) (checked : check sys frame = true) :
    Holds sys frame := by
  have facts : updateGuard sys frame = true ∧
      restrictionGuard sys frame.bindings frame.restrictionBeforeBeta frame.beforeBeta = true ∧
      restrictionGuard sys frame.bindings frame.restrictionBeforeBonus frame.beforeBonus = true ∧
      restrictionGuard sys frame.bindings frame.restrictionAfterBeta frame.preBeta = true ∧
      restrictionGuard sys frame.bindings frame.restrictionAfterBonus frame.preBonus = true ∧
      frame.numericProof < sys.numericCount ∧
      (sys.numeric frame.numericProof).claim = (template sys frame).normalize := of_decide_eq_true checked
  intro p satisfied budget decreasing
  have updates := updateGuard_sound sys frame facts.1 p
  have beforeBeta := restrictionGuard_sound sys frame.bindings _ _ facts.2.1 p satisfied
  have beforeBonus := restrictionGuard_sound sys frame.bindings _ _ facts.2.2.1 p satisfied
  have afterBeta := restrictionGuard_sound sys frame.bindings _ _ facts.2.2.2.1 p satisfied
  have afterBonus := restrictionGuard_sound sys frame.bindings _ _ facts.2.2.2.2.1 p satisfied
  have counted := erase_count sys.support frame.bindings p satisfied
  have valid := sys.numericValid frame.numericProof facts.2.2.2.2.2.1
  rw [facts.2.2.2.2.2.2] at valid
  have unnormalized := DecisionDAGCountedCompact.normalize_sound sys.read (template sys frame) valid
  have trigger : DecisionDAGCountedCompact.Trigger sys.read (template sys frame) p := by
    intro _
    change eval sys.read p (sys.restrictions frame.restrictionAfterBonus).claim.output <
      eval sys.read p (sys.restrictions frame.restrictionBeforeBonus).claim.output
    rw [afterBonus, beforeBonus, updates.2]
    exact decreasing
  have result := unnormalized p (by intro binding member; cases member) (by
    change count (eraseBindings sys.support frame.bindings) p ≤ frame.budget - charge sys.support frame.bindings
    omega) trigger
  change eval sys.read p (sys.restrictions frame.restrictionBeforeBeta).claim.output +
    eval sys.read p (sys.restrictions frame.restrictionBeforeBonus).claim.output ≤ frame.slack +
    eval sys.read p (sys.restrictions frame.restrictionAfterBeta).claim.output +
    eval sys.read p (sys.restrictions frame.restrictionAfterBonus).claim.output at result
  simpa only [beforeBeta, beforeBonus, afterBeta, afterBonus, updates.1, updates.2] using result

end NetHack.Sokoban.CountedLocalCase
