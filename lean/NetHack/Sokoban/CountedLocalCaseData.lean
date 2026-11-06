/- Data-only certificate matching, with an ordinary rfl bridge to the original
CountedLocalCase.check. Raw matching NEVER implies numeric soundness without
an actual System carrying checked U/R/N semantics. This permits independent
physical-oracle coverage work while the exhaustive table pass is running. -/
import NetHack.Sokoban.CountedLocalCase
namespace NetHack.Sokoban.CountedLocalCaseData
open DecisionDAG (Node)
open DecisionDAGTransform (Bindings)
open CountedLocalCase (Frame eraseBindings charge)
structure Data where
  read : Nat → Node
  support : List Cell
  updates : Nat → DecisionDAGTransform.UpdateRow
  updateCount : Nat
  restrictions : Nat → DecisionDAGTransform.RestrictionRow
  restrictionCount : Nat
  numeric : Nat → DecisionDAGCountedBounded.Row
  numericCount : Nat

def fromSystem (sys : CountedLocalCase.System) : Data :=
  ⟨sys.read,sys.support,sys.updates,sys.updateCount,sys.restrictions,sys.restrictionCount,sys.numeric,sys.numericCount⟩

def updateGuard (sys : Data) (frame : Frame) : Bool :=
  match frame.updateProofs with
  | none => decide (frame.changes = [] ∧ frame.preBeta = frame.afterBeta ∧ frame.preBonus = frame.afterBonus)
  | some (beta, bonus) => decide (beta < sys.updateCount ∧ bonus < sys.updateCount ∧
      (sys.updates beta).claim = ⟨frame.changes, frame.afterBeta, frame.preBeta⟩ ∧
      (sys.updates bonus).claim = ⟨frame.changes, frame.afterBonus, frame.preBonus⟩)


def restrictionGuard (sys : Data) (bindings : Bindings) (index original : Nat) : Bool :=
  decide (index < sys.restrictionCount ∧ (sys.restrictions index).claim.original = original ∧
    (sys.restrictions index).claim.bindings ⊆ bindings)


def template (sys : Data) (frame : Frame) : DecisionDAGCountedCompact.Claim :=
  ⟨[], eraseBindings sys.support frame.bindings, frame.budget - charge sys.support frame.bindings,
    (sys.restrictions frame.restrictionBeforeBeta).claim.output,
    (sys.restrictions frame.restrictionBeforeBonus).claim.output,
    (sys.restrictions frame.restrictionAfterBeta).claim.output,
    (sys.restrictions frame.restrictionAfterBonus).claim.output, frame.slack, true⟩

def check (sys : Data) (frame : Frame) : Bool :=
  decide (updateGuard sys frame = true ∧
    restrictionGuard sys frame.bindings frame.restrictionBeforeBeta frame.beforeBeta = true ∧
    restrictionGuard sys frame.bindings frame.restrictionBeforeBonus frame.beforeBonus = true ∧
    restrictionGuard sys frame.bindings frame.restrictionAfterBeta frame.preBeta = true ∧
    restrictionGuard sys frame.bindings frame.restrictionAfterBonus frame.preBonus = true ∧
    frame.numericProof < sys.numericCount ∧
    (sys.numeric frame.numericProof).claim = (template sys frame).normalize)

theorem check_fromSystem (sys : CountedLocalCase.System) (frame : Frame) :
    check (fromSystem sys) frame = CountedLocalCase.check sys frame := rfl

/-- Raw matching can be used only after the semantic table proof fields exist. -/
theorem checked_sound (sys : CountedLocalCase.System) (data : Data)
    (same : fromSystem sys = data) (frame : Frame) (checked : check data frame = true) :
    CountedLocalCase.Holds sys frame := by
  apply CountedLocalCase.checked_sound
  rw [← check_fromSystem, same]
  exact checked
end NetHack.Sokoban.CountedLocalCaseData
