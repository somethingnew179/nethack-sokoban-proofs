import Owner1007.Corral11
import NetHack.Sokoban.Generated.Soko12Potential

namespace Owner1007.PricedCorral
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
variable {n : Nat}

def Shift (board : Board) (holes : List Cell) (potential : Potential)
    (locks region : Fin n → List Cell) (credit : Fin n → Int)
    (i : Fin n) (source : Cell) (dir : Dir) : Prop :=
  ∃ j : Fin n, ∃ dest ∈ pushTargets board source dir,
    pushTargets board source dir = [dest] ∧ dest ∉ holes ∧
    locks j ⊆ dest :: (locks i).erase source ∧ source ∈ region j ∧
    credit i ≤ 1 + potential.boulder dest - potential.boulder source + credit j
instance (board : Board) (holes : List Cell) (potential : Potential)
    (locks region : Fin n → List Cell) (credit : Fin n → Int)
    (i : Fin n) (source : Cell) (dir : Dir) :
    Decidable (Shift board holes potential locks region credit i source dir) := by
  unfold Shift
  infer_instance

def Closed (board : Board) (holes : List Cell) (potential : Potential)
    (locks region : Fin n → List Cell) (credit : Fin n → Int) : Prop :=
  (∀ i hero, hero ∈ region i → ∀ dir target, advance board hero dir = some target →
    target ∈ board.floor → target ∉ board.doors → target ∉ locks i →
    corner board (PatternCorrection.project (locks i)) hero dir = false → target ∈ region i) ∧
  (∀ i hero, hero ∈ region i → ∀ dir source, source ∈ locks i →
    advance board hero dir = some source →
    BlockedPush board (locks i) source dir ∨ Shift board holes potential locks region credit i source dir)

def Good (locks region : Fin n → List Cell) (i : Fin n) (state : State) : Prop :=
  state.player ∈ region i ∧ locks i ⊆ state.boulders

theorem step_price {board : Board} {holes : List Cell} {potential : Potential}
    {locks region : Fin n → List Cell} {credit : Fin n → Int}
    (closed : Closed board holes potential locks region credit) (unique : ∀ i, (locks i).Nodup)
    (valid : Valid board potential)
    {state : State} {dir : Dir} {t : Transition} {i : Fin n}
    (good : Good locks region i state)
    (holesInside : state.holes ⊆ holes) (checked : step board state dir = some t) :
    ∃ j, Good locks region j t.state ∧
      credit i ≤ Int.ofNat t.pushCost + potential.value t.state - potential.value state + credit j := by
  obtain ⟨heroInside, inside⟩ := good
  have smallCorner := GhostProjection.original_corner_projected board state (locks i) inside dir t checked
  have nonnegative := valid.stepBound state dir t checked
  rcases step_cases_full board state dir t checked with walked | pushed
  · obtain ⟨target, adjacent, floor, notBox, notHole, shape⟩ := walked
    have door := FiniteTopology.step_target_not_door board state dir t target adjacent checked
    have notLock : target ∉ locks i := fun h => notBox (inside h)
    have targetInside := closed.1 i state.player heroInside dir target adjacent floor door notLock smallCorner
    refine ⟨i, ⟨?_, ?_⟩, ?_⟩
    · simpa only [shape] using targetInside
    · simpa only [shape] using inside
    · omega
  · obtain ⟨source, result, adjacent, floor, present, push, shape⟩ := pushed
    have first := push_first_clear board state source dir result push
    have spec := pushBoulder_spec board state source dir result push
    by_cases member : source ∈ locks i
    · rcases closed.2 i state.player heroInside dir source member adjacent with blocked | shifted
      · rcases blocked with diagonal | blocked
        · simp only [first.1] at diagonal
          contradiction
        · obtain ⟨dest, next, floor, door, empty⟩ := first.2
          simp only [next] at blocked
          rcases blocked with wall | door' | box
          · exact False.elim (wall floor)
          · exact False.elim (door door')
          · exact False.elim (empty (inside box))
      · obtain ⟨j, dest, destFloor, targets, noHole, nextLocks, nextHero, price⟩ := shifted
        have landing : result.landing = dest := by simpa only [targets, List.mem_singleton] using spec.2
        have actual : result.filled = none ∧ result.boulders = dest :: state.boulders.erase source := by
          rcases spec.1 with stay | fill
          · exact ⟨stay.1, by simpa only [landing] using stay.2⟩
          · exact False.elim (noHole (holesInside (landing ▸ fill.2.1)))
        have erased : (locks i).erase source ⊆ state.boulders.erase source := by
          intro cell found
          have parts := (unique i).mem_erase_iff.mp found
          exact (List.mem_erase_of_ne parts.1).mpr (inside parts.2)
        have effect : Matches state t (.push source (.stay dest)) := by
          refine ⟨present, ?_⟩
          simp only [shape, actual.1, actual.2, landing, afterFill]
        have delta := matches_delta potential state t (.push source (.stay dest)) effect
        simp only [slack] at delta
        refine ⟨j, ⟨?_, ?_⟩, ?_⟩
        · simpa only [shape] using nextHero
        · simp only [shape]
          change locks j ⊆ result.boulders
          rw [actual.2]
          exact List.Subset.trans nextLocks (List.cons_subset_cons dest erased)
        · omega
    · have door := FiniteTopology.step_target_not_door board state dir t source adjacent checked
      have targetInside := closed.1 i state.player heroInside dir source adjacent floor door member smallCorner
      have erased : locks i ⊆ state.boulders.erase source := by
        intro cell found
        have different : cell ≠ source := by intro same; exact member (same ▸ found)
        exact (List.mem_erase_of_ne different).mpr (inside found)
      refine ⟨i, ⟨?_, ?_⟩, ?_⟩
      · simpa only [shape] using targetInside
      · simp only [shape]
        change locks i ⊆ result.boulders
        rcases spec.1 with stay | fill
        · rw [stay.2]; exact fun _ h => List.mem_cons_of_mem _ (erased h)
        · rw [fill.2.2]; exact erased
      · omega

theorem trace_price {board : Board} {holes : List Cell} {potential : Potential}
    {locks region : Fin n → List Cell} {credit : Fin n → Int}
    (closed : Closed board holes potential locks region credit) (unique : ∀ i, (locks i).Nodup)
    (valid : Valid board potential) {initial final : State} {dirs : List Dir} {pushes moves : Nat}
    (trace : Trace board initial dirs final pushes moves) {i : Fin n}
    (good : Good locks region i initial) (holesInside : initial.holes ⊆ holes) :
    ∃ j, Good locks region j final ∧
      credit i ≤ Int.ofNat pushes + potential.value final - potential.value initial + credit j := by
  induction trace generalizing i with
  | nil => exact ⟨i, good, by simp⟩
  | cons head tail ih =>
    obtain ⟨j, nextGood, one⟩ := step_price closed unique valid good holesInside head
    obtain ⟨k, finalGood, later⟩ := ih nextGood
      (List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holesInside)
    refine ⟨k, finalGood, ?_⟩
    simp only [Int.ofNat_eq_natCast, Int.natCast_add] at *
    omega

def pushCheck (board : Board) (holes : List Cell) (potential : Potential)
    (locks region : Fin n → List Cell) (credit : Fin n → Int)
    (i : Fin n) (hero : Cell) (dir : Dir) : Bool :=
  match advance board hero dir with
  | none => true
  | some source => !(locks i).contains source ||
      decide (BlockedPush board (locks i) source dir ∨
        Shift board holes potential locks region credit i source dir)

def check (board : Board) (holes : List Cell) (potential : Potential)
    (locks region : Fin n → List Cell) (credit : Fin n → Int) : Bool :=
  (List.finRange n).all fun i => (region i).all fun hero => allDirs.all fun dir =>
    Corral11.walkCheck board locks region i hero dir &&
      pushCheck board holes potential locks region credit i hero dir

theorem closed_of_check (board : Board) (holes : List Cell) (potential : Potential)
    (locks region : Fin n → List Cell) (credit : Fin n → Int)
    (checked : check board holes potential locks region credit = true) :
    Closed board holes potential locks region credit := by
  constructor
  · intro i hero heroInside dir target adjacent floor door notLock clear
    have iInside : i ∈ List.finRange n := by simp
    have dInside : dir ∈ allDirs := by cases dir <;> simp [allDirs, cardinalDirs]
    have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp checked i iInside) hero heroInside) dir dInside
    have numeric := (Bool.and_eq_true_iff.mp row).1
    simp only [Corral11.walkCheck, adjacent] at numeric
    exact of_decide_eq_true numeric ⟨floor, door, notLock, clear⟩
  · intro i hero heroInside dir source sourceInside adjacent
    have iInside : i ∈ List.finRange n := by simp
    have dInside : dir ∈ allDirs := by cases dir <;> simp [allDirs, cardinalDirs]
    have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp checked i iInside) hero heroInside) dir dInside
    have numeric := (Bool.and_eq_true_iff.mp row).2
    simp only [pushCheck, adjacent, List.contains_iff_mem.mpr sourceInside,
      Bool.not_true, Bool.false_or] at numeric
    exact of_decide_eq_true numeric
#print axioms step_price
#print axioms trace_price
#print axioms closed_of_check
end Owner1007.PricedCorral
