import Owner1007.Locks
import Owner1007.TokenAccounting

namespace Owner1007.Corral11
open NetHack.Sokoban
open NetHack.Sokoban.HazardPattern
variable {n : Nat}

def Shift (board : Board) (holes : List Cell) (locks region : Fin n → List Cell)
    (i : Fin n) (source : Cell) (dir : Dir) : Prop :=
  ∃ j : Fin n, ∃ dest ∈ pushTargets board source dir, pushTargets board source dir = [dest] ∧
    dest ∉ holes ∧ locks j ⊆ dest :: (locks i).erase source ∧ source ∈ region j

instance (board : Board) (holes : List Cell) (locks region : Fin n → List Cell)
    (i : Fin n) (source : Cell) (dir : Dir) : Decidable (Shift board holes locks region i source dir) := by
  unfold Shift
  infer_instance

def Closed (board : Board) (holes : List Cell) (locks region : Fin n → List Cell) : Prop :=
  (∀ i hero, hero ∈ region i → ∀ dir target, advance board hero dir = some target →
    target ∈ board.floor → target ∉ board.doors → target ∉ locks i →
    corner board (PatternCorrection.project (locks i)) hero dir = false → target ∈ region i) ∧
  (∀ i hero, hero ∈ region i → ∀ dir source, source ∈ locks i →
    advance board hero dir = some source →
    BlockedPush board (locks i) source dir ∨ Shift board holes locks region i source dir)

def Good (locks region : Fin n → List Cell) (state : State) : Prop :=
  ∃ i, state.player ∈ region i ∧ locks i ⊆ state.boulders

/-- A small family of occupancy cuts can shift while retaining its trapped
stone count. The player's actual component is part of the invariant. -/
theorem step_good {board : Board} {holes : List Cell} {locks region : Fin n → List Cell}
    (closed : Closed board holes locks region) (unique : ∀ i, (locks i).Nodup)
    {state : State} {dir : Dir} {t : Transition} (good : Good locks region state)
    (holesInside : state.holes ⊆ holes) (checked : step board state dir = some t) :
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

theorem trace_good {board : Board} {holes : List Cell} {locks region : Fin n → List Cell}
    (closed : Closed board holes locks region) (unique : ∀ i, (locks i).Nodup)
    {initial final : State} {dirs : List Dir} {pushes moves : Nat}
    (trace : Trace board initial dirs final pushes moves)
    (good : Good locks region initial) (holesInside : initial.holes ⊆ holes) : Good locks region final := by
  induction trace with
  | nil => exact good
  | cons head tail ih =>
    exact ih (step_good closed unique good holesInside head)
      (List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holesInside)

def walkCheck (board : Board) (locks region : Fin n → List Cell) (i : Fin n) (hero : Cell) (dir : Dir) : Bool :=
  match advance board hero dir with
  | none => true
  | some target => decide ((target ∈ board.floor ∧ target ∉ board.doors ∧ target ∉ locks i ∧
      corner board (PatternCorrection.project (locks i)) hero dir = false) → target ∈ region i)

def check (board : Board) (holes : List Cell) (locks region : Fin n → List Cell) : Bool :=
  (List.finRange n).all fun i => (region i).all fun hero => allDirs.all fun dir =>
    walkCheck board locks region i hero dir &&
      (locks i).all fun source => decide (advance board hero dir ≠ some source ∨
        BlockedPush board (locks i) source dir ∨ Shift board holes locks region i source dir)

theorem closed_of_check (board : Board) (holes : List Cell) (locks region : Fin n → List Cell)
    (checked : check board holes locks region = true) : Closed board holes locks region := by
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

def regionBase : List Cell :=
  [27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,
   53,54,55,56,57,58,59,76,85,102,106,107,108,109,110,111,112,113,114,115,116,
   128,132,133,134,135,136,137,138,139,140,141,142,154,164,180,190,191,192,193,
   194,206,215,216,217,218,219,220,232,258,284,310,336,362]

def locks (i : Fin 3) : List Cell := [188,189,213,214+i.val]
def region (i : Fin 3) : List Cell :=
  regionBase.filter fun cell => !(decide (215 ≤ cell ∧ cell ≤ 214+i.val))

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked : check soko1_1.board soko1_1.initial.holes locks region = true := by
  decide +kernel

theorem closed : Closed soko1_1.board soko1_1.initial.holes locks region :=
  closed_of_check _ _ _ _ checked

theorem unique (i : Fin 3) : (locks i).Nodup := by
  have all : (List.finRange 3).all (fun i => decide ((locks i).Nodup)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))

/-- A three-phase occupancy cut, with at most two permitted west pushes.
All four trapped stones persist in the unchanged original Model. -/
theorem excluded {state final : State} {history dirs : List Dir}
    {previousPushes previousMoves pushes moves : Nat}
    (reached : Trace soko1_1.board soko1_1.initial history state previousPushes previousMoves)
    (tail : Trace soko1_1.board state dirs final pushes moves) (completed : Goal final) :
    ¬ Good locks region state := by
  intro good
  have holesInside : state.holes ⊆ soko1_1.initial.holes := reached.holes_sublist.subset
  obtain ⟨i, _, persists⟩ := trace_good closed unique tail good holesInside
  have cardinality := List.Nodup.length_le_of_subset (unique i) persists
  have prefixConserved := reached.conservation
  have suffixConserved := tail.conservation
  have empty : final.holes = [] := completed
  change 18 + state.holes.length = state.boulders.length + 16 at prefixConserved
  rw [empty] at suffixConserved
  change 4 ≤ final.boulders.length at cardinality
  simp only [List.length_nil] at suffixConserved
  omega

#print axioms step_good
#print axioms trace_good
#print axioms closed_of_check
#print axioms excluded
end Owner1007.Corral11
