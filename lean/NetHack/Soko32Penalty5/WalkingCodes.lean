/- Precomputed physical geometry only. Boolean occupancy and the BOTH-side
corner rule remain explicit. Soundness is proved for arbitrary box lists. -/
import NetHack.Soko32Penalty5.Certificate
namespace NetHack.Soko32Penalty5
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.PatternCorrection

inductive BlockCode where
  | wall
  | box (cell : Cell)
  deriving BEq, DecidableEq, Repr
def BlockCode.blocked (boxes : List Cell) : BlockCode → Bool
  | .wall => true
  | .box c => boxes.contains c
def sideCode (hero : Cell) (dir : Dir) : BlockCode :=
  match advance soko3_2.board hero dir with
  | none => .wall
  | some c => if !soko3_2.board.floor.contains c && !soko3_2.board.doors.contains c then .wall else .box c
structure WalkCode where
  hero : Cell
  target : Cell
  diagonal : Bool
  first : BlockCode
  second : BlockCode
  deriving BEq, DecidableEq, Repr
def code (hero : Cell) (dir : Dir) : Option WalkCode := do
  let target ← advance soko3_2.board hero dir
  if !soko3_2.board.floor.contains target || soko3_2.board.doors.contains target then none
  else some ⟨hero,target,dir.diagonal,sideCode hero dir.sides.1,sideCode hero dir.sides.2⟩
def WalkCode.enabled (boxes : List Cell) (a : WalkCode) : Bool :=
  !boxes.contains a.target && !(a.diagonal && a.first.blocked boxes && a.second.blocked boxes)

theorem side_exact (boxes : List Cell) (hero : Cell) (dir : Dir) :
    (sideCode hero dir).blocked boxes =
      (match advance soko3_2.board hero dir with
       | none => true
       | some c => (!soko3_2.board.floor.contains c && !soko3_2.board.doors.contains c) || project boxes c) := by
  unfold sideCode
  split
  · rfl
  · split <;> simp_all [BlockCode.blocked,project]

theorem code_covers (boxes : List Cell) (hero : Cell) (dir : Dir) (target : Cell)
    (walked : walking boxes hero dir = some target) :
    ∃ a, code hero dir = some a ∧ a.hero = hero ∧ a.target = target ∧ a.enabled boxes = true := by
  cases heroBox : project boxes hero with
  | true => simp [walking,stepOracle,heroBox] at walked
  | false =>
    cases adjacent : advance soko3_2.board hero dir with
    | none => simp [walking,stepOracle,heroBox,adjacent] at walked
    | some next =>
      cases floor : soko3_2.board.floor.contains next <;>
        cases door : soko3_2.board.doors.contains next <;>
        cases corner : HazardPattern.corner soko3_2.board (project boxes) hero dir <;>
        simp only [walking,stepOracle,heroBox,adjacent,floor,door,corner,
          Bool.false_or,Bool.true_or,Bool.not_true,Bool.not_false,Bool.false_eq_true,
          ↓reduceIte,bind,pure,Option.bind_some] at walked
      all_goals first | contradiction | skip
      cases box : project boxes next with
      | true =>
        cases push : pushOracle soko3_2.board (project boxes) (fun _ => false) next dir <;>
          simp [box,push] at walked
      | false =>
        have same : next = target := by simpa only [box,Bool.false_eq_true,↓reduceIte,Option.some.injEq] using walked
        subst target
        let a : WalkCode := ⟨hero,next,dir.diagonal,sideCode hero dir.sides.1,sideCode hero dir.sides.2⟩
        refine ⟨a,by simp only [code,adjacent,bind,pure,Option.bind_some,floor,door,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte]; rfl,rfl,rfl,?_⟩
        have sides : (dir.diagonal && (sideCode hero dir.sides.1).blocked boxes &&
            (sideCode hero dir.sides.2).blocked boxes) = false := by
          rw [side_exact,side_exact]
          exact corner
        simp only [WalkCode.enabled,a,sides,Bool.not_false,Bool.and_true]
        exact congrArg Bool.not box

def fastWalkCheck (codes : List WalkCode) (r : Row) : Bool := codes.all fun a =>
  if r.reach.testBit a.hero && !r.reach.testBit a.target then !a.enabled r.boxes else true

theorem fast_implies_walk (heroes : List Cell) (codes : List WalkCode)
    (coverage : ∀ hero ∈ heroes, ∀ dir a, code hero dir = some a → a ∈ codes)
    (targets : ∀ a ∈ codes, a.target ∈ heroes) (r : Row)
    (checked : fastWalkCheck codes r = true) : walkCheck heroes r = true := by
  apply List.all_eq_true.mpr
  intro hero member
  cases present : r.reach.testBit hero with
  | false => simp [present]
  | true =>
    simp only [present,↓reduceIte]
    apply List.all_eq_true.mpr
    intro dir _
    cases walked : walking r.boxes hero dir with
    | none => rfl
    | some target =>
      obtain ⟨a,found,source,destination,enabled⟩ := code_covers r.boxes hero dir target walked
      have inside := coverage hero member dir a found
      have row := List.all_eq_true.mp checked a inside
      have atTarget : r.reach.testBit target = true := by
        cases hit : r.reach.testBit target with
        | true => rfl
        | false => simp [source,destination,present,hit,enabled] at row
      have targetMember : target ∈ heroes := destination ▸ targets a inside
      simp [targetMember,atTarget]

end NetHack.Soko32Penalty5
