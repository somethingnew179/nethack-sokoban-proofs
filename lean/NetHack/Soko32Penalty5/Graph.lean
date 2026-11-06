/- Weighted ghost-group relaxation for original soko3-2. Costs are static
potential SLACK, not pushes. Hazards do not block walking in this relaxation.
Forgetting a boulder at an explicitly listed discard is a relaxation only.
The original Model and its goal remain unchanged. -/
import NetHack.Soko32SAT.Frames
import NetHack.Sokoban.StatePermutation
import NetHack.Sokoban.IndexedCertificateTable
namespace NetHack.Soko32Penalty5
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.PatternCorrection

structure Action where
  hero : Cell
  source : Cell
  landing : Option Cell
  discard : Bool
  cost : Nat
  deriving BEq, DecidableEq, Repr

def Action.after (a : Action) (boxes : List Cell) : List Cell :=
  match a.landing with
  | none => boxes.erase a.source
  | some c => if a.discard then boxes.erase a.source else c :: boxes.erase a.source

def Action.enabled (a : Action) (boxes : List Cell) (hero : Cell) : Prop :=
  hero = a.hero ∧ a.source ∈ boxes ∧ (match a.landing with | none => True | some c => c ∉ boxes)
instance (a : Action) (boxes : List Cell) (hero : Cell) : Decidable (a.enabled boxes hero) := by
  unfold Action.enabled
  cases a.landing <;> dsimp <;> infer_instance

def walking (boxes : List Cell) (hero : Cell) (direction : Dir) : Option Cell :=
  match stepOracle soko3_2.board (project boxes) (fun _ => false) hero direction with
  | some (.walk target) => some target
  | _ => none

inductive Edge (actions : List Action) : List Cell → Cell → List Cell → Cell → Nat → Prop where
  | walk {boxes hero direction target} (checked : walking boxes hero direction = some target) :
      Edge actions boxes hero boxes target 0
  | push {boxes hero} (a : Action) (member : a ∈ actions) (legal : a.enabled boxes hero) :
      Edge actions boxes hero (a.after boxes) a.source a.cost

inductive Path (actions : List Action) : List Cell → Cell → List Cell → Cell → Nat → Prop where
  | nil (boxes hero) : Path actions boxes hero boxes hero 0
  | cons {boxes hero middle actor final finish first rest}
      (head : Edge actions boxes hero middle actor first)
      (tail : Path actions middle actor final finish rest) :
      Path actions boxes hero final finish (first + rest)

theorem enabled_perm (a : Action) {xs ys : List Cell} (same : xs.Perm ys) (hero : Cell) :
    a.enabled xs hero ↔ a.enabled ys hero := by
  unfold Action.enabled
  cases a.landing <;> simp only [same.mem_iff]

theorem after_perm (a : Action) {xs ys : List Cell} (same : xs.Perm ys) :
    (a.after xs).Perm (a.after ys) := by
  unfold Action.after
  cases a.landing with
  | none => exact same.erase _
  | some c =>
    cases h : a.discard <;> simp only [h,Bool.false_eq_true,↓reduceIte]
    · exact (same.erase _).cons _
    · exact same.erase _

theorem walking_perm {xs ys : List Cell} (same : xs.Perm ys) (hero : Cell) (dir : Dir) :
    walking xs hero dir = walking ys hero dir := by
  have projects : project xs = project ys := by funext c; exact same.contains_eq
  simp only [walking,projects]

end NetHack.Soko32Penalty5
