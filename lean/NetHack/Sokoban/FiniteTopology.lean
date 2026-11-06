/- Sparse residual certificates. A checked static topology covers every
floor-to-floor Model adjacency. Walk inequalities are checked directly;
every possible cardinal push at a positive hero is covered by a literal
FiniteMatrix edge. This proves the reduction and does not trust proposer
player regions or a push-graph search. -/
import NetHack.Sokoban.FiniteMatrix

set_option linter.unusedSimpArgs false
namespace NetHack.Sokoban.FiniteTopology
open LowerBounds FiniteResidual

structure Arc where
  direction : Dir
  target : Cell

structure TopologyRow where
  hero : Cell
  arcs : List Arc

structure PushSlot where
  hero : Cell
  edge : FiniteMatrix.Edge

def topologyCheck (board : Board) (topology : List TopologyRow) : Bool :=
  board.floor.all fun hero => allDirs.all fun d =>
    match advance board hero d with
    | none => true
    | some target => !board.floor.contains target || topology.any fun row =>
        decide (row.hero = hero) && row.arcs.any fun arc =>
          decide (arc.direction = d ∧ arc.target = target)

theorem topologyCheck_sound (board : Board) (topology : List TopologyRow)
    (checked : topologyCheck board topology = true)
    (hero : Cell) (standing : hero ∈ board.floor) (direction : Dir) (target : Cell)
    (adjacent : advance board hero direction = some target) (floor : target ∈ board.floor) :
    ∃ row, row ∈ topology ∧ row.hero = hero ∧
      ∃ arc, arc ∈ row.arcs ∧ arc.direction = direction ∧ arc.target = target := by
  have directions := List.all_eq_true.mp checked hero standing
  have member : direction ∈ allDirs := by cases direction <;> simp [allDirs, cardinalDirs]
  have selected := List.all_eq_true.mp directions direction member
  simp only [adjacent, List.contains_iff_mem.mpr floor, Bool.not_true, Bool.false_or] at selected
  rcases List.any_eq_true.mp selected with ⟨row, present, matched⟩
  have parts := Bool.and_eq_true_iff.mp matched
  have heroEq : row.hero = hero := of_decide_eq_true parts.1
  rcases List.any_eq_true.mp parts.2 with ⟨arc, arcMem, matched⟩
  have same : arc.direction = direction ∧ arc.target = target := of_decide_eq_true matched
  exact ⟨row, present, heroEq, arc, arcMem, same⟩

def walkCheck (board : Board) (entry : Entry) (hero : Cell) (arc : Arc) : Bool :=
  decide (entry.score hero ≤ entry.score arc.target) ||
    entry.boulders.contains arc.target || entry.holes.contains arc.target ||
    board.doors.contains arc.target || cornerBlocked board (entry.at hero) arc.direction

def pushCovered (board : Board) (base : State → Int) (normalize : State → State)
    (key : State → Nat) (evaluate : State → Nat → Nat)
    (entry : Entry) (slots : List PushSlot) (hero : Cell) (arc : Arc) : Bool :=
  arc.direction.diagonal || !entry.boulders.contains arc.target || slots.any fun slot =>
    decide (slot.hero = hero ∧ slot.edge.direction = arc.direction) &&
      FiniteMatrix.edgeCheck board base normalize key evaluate entry slot.hero slot.edge

def rowCheck (board : Board) (base : State → Int) (normalize : State → State)
    (key : State → Nat) (evaluate : State → Nat → Nat)
    (entry : Entry) (slots : List PushSlot) (row : TopologyRow) : Bool :=
  if entry.score row.hero = 0 then true else row.arcs.all fun arc =>
    walkCheck board entry row.hero arc &&
      pushCovered board base normalize key evaluate entry slots row.hero arc

def check (board : Board) (base : State → Int) (normalize : State → State)
    (key : State → Nat) (evaluate : State → Nat → Nat)
    (entry : Entry) (slots : List PushSlot) (topology : List TopologyRow) : Bool :=
  topology.all (rowCheck board base normalize key evaluate entry slots)

private def rawCore (board : Board) (s : State) (d : Dir) : Option Transition := do
  if goal s then none else pure ()
  let target ← advance board s.player d
  if !board.floor.contains target || board.doors.contains target || cornerBlocked board s d then
    none else pure ()
  if s.boulders.contains target then
    let p ← pushBoulder board s target d
    return {state := {player := target, boulders := p.boulders, holes := afterFill s.holes p.filled}, pushed := true, filled := p.filled, pushSource := some target, landing := some p.landing}
  else
    if s.holes.contains target then none
    else return {state := {s with player := target}, pushed := false, filled := none}

theorem step_corner_clear (board : Board) (s : State) (d : Dir) (t : Transition)
    (checked : step board s d = some t) : cornerBlocked board s d = false := by
  have core : rawCore board s d = some t := step_core_of board s d t checked
  cases corner : cornerBlocked board s d with
  | false => rfl
  | true =>
    cases completed : goal s <;> cases adjacent : advance board s.player d <;>
      simp [rawCore, corner, completed, adjacent] at core

theorem step_target_not_door (board : Board) (s : State) (d : Dir) (t : Transition)
    (target : Cell) (adjacent : advance board s.player d = some target)
    (checked : step board s d = some t) : target ∉ board.doors := by
  have core : rawCore board s d = some t := step_core_of board s d t checked
  intro door
  cases completed : goal s <;> simp [rawCore, completed, adjacent, door] at core

theorem check_sound (board : Board) (base : State → Int)
    (normalizer : Normalizer board) (normalize : State → State)
    (table : Table) (key : State → Nat) (evaluate : State → Nat → Nat)
    (entry : Entry) (slots : List PushSlot) (topology : List TopologyRow)
    (valid : StepBound board base)
    (normalizerEq : ∀ s, normalizer.normalize s = normalize s)
    (evaluateEq : ∀ s, evaluate s (key s) = rawBonus table key s)
    (honest : ∀ p, rawBonus table key (normalizer.normalize (entry.at p)) = entry.score p)
    (staticChecked : topologyCheck board topology = true)
    (checked : check board base normalize key evaluate entry slots topology = true) :
    RowBound board base normalizer table key entry := by
  intro hero positive direction t first
  have standing := (step_player_clear board (entry.at hero) direction t first).1
  have corner := step_corner_clear board (entry.at hero) direction t first
  have chosen (target : Cell) (adjacent : advance board hero direction = some target)
      (floor : target ∈ board.floor) :
      ∃ row, row ∈ topology ∧ row.hero = hero ∧
        ∃ arc, arc ∈ row.arcs ∧ arc.direction = direction ∧ arc.target = target ∧
          walkCheck board entry hero arc = true ∧
          pushCovered board base normalize key evaluate entry slots hero arc = true := by
    rcases topologyCheck_sound board topology staticChecked hero standing direction target adjacent floor with
      ⟨row, rowMem, heroEq, arc, arcMem, dirEq, targetEq⟩
    have rowChecked := List.all_eq_true.mp checked row rowMem
    have scoreNonzero : ¬entry.score row.hero = 0 := by rw [heroEq]; omega
    simp only [rowCheck, scoreNonzero, ↓reduceIte] at rowChecked
    have both := Bool.and_eq_true_iff.mp (List.all_eq_true.mp rowChecked arc arcMem)
    rw [heroEq] at both
    exact ⟨row, rowMem, heroEq, arc, arcMem, dirEq, targetEq, both⟩
  rcases step_cases_full board (entry.at hero) direction t first with walk | push
  · rcases walk with ⟨target, adjacent, floor, boxClear, holeClear, shape⟩
    change target ∉ entry.boulders at boxClear
    change target ∉ entry.holes at holeClear
    rcases chosen target adjacent floor with ⟨_, _, _, arc, _, dirEq, targetEq, walkChecked, _⟩
    have door := step_target_not_door board (entry.at hero) direction t target adjacent first
    have scores : entry.score hero ≤ entry.score target := by
      simpa only [walkCheck, dirEq, targetEq,
        show entry.boulders.contains target = false by simp [boxClear],
        show entry.holes.contains target = false by simp [holeClear],
        show board.doors.contains target = false by simp [door], corner,
        Bool.or_false, decide_eq_true_eq] using walkChecked
    have bound := valid (entry.at hero) direction t first
    subst t
    change base (entry.at hero) + Int.ofNat (entry.score hero) ≤
      _ + base (entry.at target) + Int.ofNat (rawBonus table key (normalizer.normalize (entry.at target)))
    rw [honest]
    change base (entry.at hero) ≤ Int.ofNat 0 + base (entry.at target) at bound
    simp only [Int.ofNat_eq_natCast] at bound ⊢
    omega
  · rcases push with ⟨source, result, adjacent, floor, present, pushed, shape⟩
    change source ∈ entry.boulders at present
    have diagonal : direction.diagonal = false := by
      cases hd : direction.diagonal with
      | false => rfl
      | true => simp [pushBoulder, hd] at pushed
    rcases chosen source adjacent floor with ⟨_, _, _, arc, _, dirEq, targetEq, _, pushChecked⟩
    simp only [pushCovered, dirEq, targetEq, diagonal, List.contains_iff_mem.mpr present,
      Bool.not_true, Bool.false_or] at pushChecked
    rcases List.any_eq_true.mp pushChecked with ⟨slot, _, selected⟩
    have parts := Bool.and_eq_true_iff.mp selected
    have same : slot.hero = hero ∧ slot.edge.direction = direction := of_decide_eq_true parts.1
    have bound := FiniteMatrix.edgeCheck_sound board base normalizer normalize table key evaluate
      entry slot.hero slot.edge valid normalizerEq evaluateEq honest parts.2 t
    simpa only [same.1, same.2] using bound (by simpa only [same.1, same.2] using first)

end NetHack.Sokoban.FiniteTopology
