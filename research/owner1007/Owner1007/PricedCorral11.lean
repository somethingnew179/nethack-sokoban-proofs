import Owner1007.Corral11

namespace Owner1007.PricedCorral11
open NetHack.Sokoban
open NetHack.Sokoban.HazardPattern
open Owner1007.Corral11
variable {n : Nat}

def PaidStep (paid : Cell → Dir → Prop) (dir : Dir) (t : Transition) : Prop :=
  ∃ source, t.pushSource = some source ∧ paid source dir

def ClosedExcept (board : Board) (holes : List Cell) (locks region : Fin n → List Cell)
    (paid : Cell → Dir → Prop) : Prop :=
  (∀ i hero, hero ∈ region i → ∀ dir target, advance board hero dir = some target →
    target ∈ board.floor → target ∉ board.doors → target ∉ locks i →
    corner board (PatternCorrection.project (locks i)) hero dir = false → target ∈ region i) ∧
  (∀ i hero, hero ∈ region i → ∀ dir source, source ∈ locks i →
    advance board hero dir = some source →
    BlockedPush board (locks i) source dir ∨ paid source dir ∨ Shift board holes locks region i source dir)

theorem step_good_except {board : Board} {holes : List Cell} {locks region : Fin n → List Cell} {paid : Cell → Dir → Prop}
    (closed : ClosedExcept board holes locks region paid) (unique : ∀ i, (locks i).Nodup)
    {state : State} {dir : Dir} {t : Transition} (good : Good locks region state)
    (holesInside : state.holes ⊆ holes) (checked : step board state dir = some t) (avoid : ¬ PaidStep paid dir t) :
    Good locks region t.state := by
  obtain ⟨i, heroInside, inside⟩ := good
  have smallCorner := GhostProjection.original_corner_projected board state (locks i) inside dir t checked
  rcases step_cases_full board state dir t checked with walked | pushed
  · obtain ⟨target, adjacent, floor, notBox, notHole, shape⟩ := walked
    have door := FiniteTopology.step_target_not_door board state dir t target adjacent checked
    have notLock : target ∉ locks i := fun h => notBox (inside h)
    have targetInside := closed.1 i state.player heroInside dir target adjacent floor door notLock smallCorner
    exact ⟨i, by simpa only [shape] using targetInside, by simpa only [shape] using inside⟩
  · obtain ⟨source, result, adjacent, floor, present, push, shape⟩ := pushed
    have first := push_first_clear board state source dir result push
    have spec := pushBoulder_spec board state source dir result push
    by_cases member : source ∈ locks i
    · have neverPays : ¬ paid source dir := by
        intro pays
        apply avoid
        exact ⟨source, by simp only [shape], pays⟩
      have choice : BlockedPush board (locks i) source dir ∨ Shift board holes locks region i source dir := by
        rcases closed.2 i state.player heroInside dir source member adjacent with blocked | pays | shifted
        · exact Or.inl blocked
        · exact False.elim (neverPays pays)
        · exact Or.inr shifted
      rcases choice with blocked | shifted
      · rcases blocked with diagonal | blocked
        · simp only [first.1] at diagonal
          contradiction
        · obtain ⟨dest, next, floor, door, empty⟩ := first.2
          simp only [next] at blocked
          rcases blocked with wall | door' | box
          · exact False.elim (wall floor)
          · exact False.elim (door door')
          · exact False.elim (empty (inside box))
      · obtain ⟨j, dest, destFloor, targets, noHole, nextLocks, nextHero⟩ := shifted
        have landing : result.landing = dest := by simpa only [targets, List.mem_singleton] using spec.2
        have boxes : result.boulders = dest :: state.boulders.erase source := by
          rcases spec.1 with stay | fill
          · simpa only [landing] using stay.2
          · exact False.elim (noHole (holesInside (landing ▸ fill.2.1)))
        have erased : (locks i).erase source ⊆ state.boulders.erase source := by
          intro cell found
          have parts := (unique i).mem_erase_iff.mp found
          exact (List.mem_erase_of_ne parts.1).mpr (inside parts.2)
        refine ⟨j, by simpa only [shape] using nextHero, ?_⟩
        simp only [shape]
        change locks j ⊆ result.boulders
        rw [boxes]
        exact List.Subset.trans nextLocks (List.cons_subset_cons dest erased)
    · have door := FiniteTopology.step_target_not_door board state dir t source adjacent checked
      have targetInside := closed.1 i state.player heroInside dir source adjacent floor door member smallCorner
      have erased : locks i ⊆ state.boulders.erase source := by
        intro cell found
        have different : cell ≠ source := by intro same; exact member (same ▸ found)
        exact (List.mem_erase_of_ne different).mpr (inside found)
      refine ⟨i, by simpa only [shape] using targetInside, ?_⟩
      simp only [shape]
      change locks i ⊆ result.boulders
      rcases spec.1 with stay | fill
      · rw [stay.2]; exact fun _ h => List.mem_cons_of_mem _ (erased h)
      · rw [fill.2.2]; exact erased

inductive PaidTrace (board : Board) (paid : Cell → Dir → Prop) :
    State → List Dir → State → Nat → Nat → Prop where
  | head {state dir t rest final pushes moves}
      (checked : step board state dir = some t) (pays : PaidStep paid dir t)
      (tail : Trace board t.state rest final pushes moves) :
      PaidTrace board paid state (dir :: rest) final (t.pushCost + pushes) (1 + moves)
  | tail {state dir t rest final pushes moves}
      (checked : step board state dir = some t)
      (later : PaidTrace board paid t.state rest final pushes moves) :
      PaidTrace board paid state (dir :: rest) final (t.pushCost + pushes) (1 + moves)

theorem PaidTrace.trace {board paid initial dirs final pushes moves}
    (found : PaidTrace board paid initial dirs final pushes moves) :
    Trace board initial dirs final pushes moves := by
  induction found with
  | head checked pays tail => exact .cons checked tail
  | tail checked later ih => exact .cons checked ih

theorem event_or_good {board : Board} {holes : List Cell} {locks region : Fin n → List Cell}
    {paid : Cell → Dir → Prop}
    (closed : ClosedExcept board holes locks region paid) (unique : ∀ i, (locks i).Nodup)
    {initial final : State} {dirs : List Dir} {pushes moves : Nat}
    (trace : Trace board initial dirs final pushes moves)
    (good : Good locks region initial) (holesInside : initial.holes ⊆ holes) :
    PaidTrace board paid initial dirs final pushes moves ∨ Good locks region final := by
  induction trace with
  | nil => exact Or.inr good
  | @cons state dir t rest final pushes moves head tail ih =>
    by_cases pays : PaidStep paid dir t
    · exact Or.inl (.head head pays tail)
    · have next := step_good_except closed unique good holesInside head pays
      have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holesInside
      rcases ih next nextHoles with found | finalGood
      · exact Or.inl (.tail head found)
      · exact Or.inr finalGood

def checkExcept (board : Board) (holes : List Cell) (locks region : Fin n → List Cell)
    (paid : Cell → Dir → Prop) [∀ c d, Decidable (paid c d)] : Bool :=
  (List.finRange n).all fun i => (region i).all fun hero => allDirs.all fun dir =>
    walkCheck board locks region i hero dir &&
      (locks i).all fun source => decide (advance board hero dir ≠ some source ∨
        BlockedPush board (locks i) source dir ∨ paid source dir ∨ Shift board holes locks region i source dir)

theorem closed_of_checkExcept (board : Board) (holes : List Cell) (locks region : Fin n → List Cell)
    (paid : Cell → Dir → Prop) [∀ c d, Decidable (paid c d)]
    (checked : checkExcept board holes locks region paid = true) : ClosedExcept board holes locks region paid := by
  constructor
  · intro i hero heroInside dir target adjacent floor door notLock clear
    have iInside : i ∈ List.finRange n := by simp
    have dInside : dir ∈ allDirs := by cases dir <;> simp [allDirs, cardinalDirs]
    have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp checked i iInside) hero heroInside) dir dInside
    have numeric := (Bool.and_eq_true_iff.mp row).1
    simp only [walkCheck, adjacent] at numeric
    exact of_decide_eq_true numeric ⟨floor, door, notLock, clear⟩
  · intro i hero heroInside dir source sourceInside adjacent
    have iInside : i ∈ List.finRange n := by simp
    have dInside : dir ∈ allDirs := by cases dir <;> simp [allDirs, cardinalDirs]
    have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp checked i iInside) hero heroInside) dir dInside
    have numeric := (Bool.and_eq_true_iff.mp row).2
    have entry := of_decide_eq_true (List.all_eq_true.mp numeric source sourceInside)
    exact entry.resolve_left (fun different => different adjacent)

def paid (source : Cell) (dir : Dir) : Prop :=
  (source = 188 ∧ dir = .west) ∨ (source = 213 ∧ dir = .west) ∨ (source = 216 ∧ dir = .east)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by
  unfold paid
  infer_instance

def locks (i : Fin 3) : List Cell := [188,192,193,213,214+i.val]
def regionBase : List Cell :=
  (Corral11.regionBase.filter fun cell => !(decide (cell = 192 ∨ cell = 193))) ++ [189]
def region (i : Fin 3) : List Cell :=
  match i.val with
  | 0 => regionBase
  | 1 => regionBase.filter fun cell => !(decide (cell = 215))
  | _ => (regionBase.filter fun cell => !(decide (cell = 216))) ++ [214]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def checkNode (i : Fin 3) : Bool :=
  (region i).all fun hero => allDirs.all fun dir =>
    walkCheck soko1_1.board locks region i hero dir &&
      (locks i).all fun source => decide (advance soko1_1.board hero dir ≠ some source ∨
        BlockedPush soko1_1.board (locks i) source dir ∨ paid source dir ∨
        Shift soko1_1.board soko1_1.initial.holes locks region i source dir)

theorem checked0 : checkNode ⟨0, by decide⟩ = true := by decide +kernel
theorem checked1 : checkNode ⟨1, by decide⟩ = true := by decide +kernel
theorem checked2 : checkNode ⟨2, by decide⟩ = true := by decide +kernel

theorem checked : checkExcept soko1_1.board soko1_1.initial.holes locks region paid = true := by
  change (List.finRange 3).all checkNode = true
  apply List.all_eq_true.mpr
  intro i _
  obtain ⟨i, bound⟩ := i
  have choices : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases choices with rfl | rfl | rfl
  · exact checked0
  · exact checked1
  · exact checked2

theorem closed : ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
  closed_of_checkExcept _ _ _ _ _ checked

theorem unique (i : Fin 3) : (locks i).Nodup := by
  have all : (List.finRange 3).all (fun i => decide ((locks i).Nodup)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))

/-- Every completing suffix from this five-stone cut must cross a specified paid exit. -/
theorem completing_contains_paid {state final : State} {history dirs : List Dir}
    {previousPushes previousMoves pushes moves : Nat}
    (reached : Trace soko1_1.board soko1_1.initial history state previousPushes previousMoves)
    (tail : Trace soko1_1.board state dirs final pushes moves) (completed : Goal final)
    (good : Good locks region state) : PaidTrace soko1_1.board paid state dirs final pushes moves := by
  have holesInside : state.holes ⊆ soko1_1.initial.holes := reached.holes_sublist.subset
  rcases event_or_good closed unique tail good holesInside with found | finalGood
  · exact found
  · obtain ⟨i, _, persists⟩ := finalGood
    have cardinality := List.Nodup.length_le_of_subset (unique i) persists
    have prefixConserved := reached.conservation
    have suffixConserved := tail.conservation
    have empty : final.holes = [] := completed
    change 18 + state.holes.length = state.boulders.length + 16 at prefixConserved
    rw [empty] at suffixConserved
    change 5 ≤ final.boulders.length at cardinality
    simp only [List.length_nil] at suffixConserved
    omega

#print axioms step_good_except
#print axioms completing_contains_paid
end Owner1007.PricedCorral11
