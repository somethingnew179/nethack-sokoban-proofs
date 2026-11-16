import Owner1007.ZeroWord11ChecksA
import Owner1007.ZeroWord11ChecksB

namespace Owner1007.ZeroWord11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.PatternCorrection
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem all_nodes (i : Nat) (active : i < 28) : nodeCheck i = true := by
  have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
    i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
    i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
    i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact node0
  · exact node1
  · exact node2
  · exact node3
  · exact node4
  · exact node5
  · exact node6
  · exact node7
  · exact node8
  · exact node9
  · exact node10
  · exact node11
  · exact node12
  · exact node13
  · exact node14
  · exact node15
  · exact node16
  · exact node17
  · exact node18
  · exact node19
  · exact node20
  · exact node21
  · exact node22
  · exact node23
  · exact node24
  · exact node25
  · exact node26
  · exact node27

theorem walk_sound (i : Nat) (checked : nodeCheck i = true)
    (hero : Cell) (inside : hero ∈ region i) (dir : Dir) (target : Cell)
    (adjacent : advance soko1_1.board hero dir = some target)
    (floor : target ∈ soko1_1.board.floor) (door : target ∉ soko1_1.board.doors)
    (different : target ≠ cell i) (hole : target ∉ soko1_1.initial.holes)
    (clear : corner soko1_1.board (project [cell i]) hero dir = false) :
    Next i (.walk target) := by
  have numeric := (Bool.and_eq_true_iff.mp checked).1
  have row := List.all_eq_true.mp (List.all_eq_true.mp numeric hero inside) dir (Geometry.all_directions dir)
  simp only [adjacent] at row
  exact of_decide_eq_true row ⟨floor,door,different,hole,clear⟩

theorem push_sound (i : Nat) (checked : nodeCheck i = true)
    (hero : Cell) (inside : hero ∈ region i) (dir : Dir) (ending : Ending)
    (behind : advance soko1_1.board (cell i) dir.opposite = some hero)
    (oracle : pushOracle soko1_1.board HazardPhases.emptyBoxes
      (project soko1_1.initial.holes) (cell i) dir = some ending)
    (zero : singleSlack hero (cell i) (.push (cell i) ending) = 0) :
    Next i (.push (cell i) ending) := by
  have numeric := (Bool.and_eq_true_iff.mp checked).2
  have row := List.all_eq_true.mp numeric dir (Geometry.all_directions dir)
  simp only [behind, if_pos inside, oracle] at row
  exact (of_decide_eq_true row).resolve_left (fun different => different zero)

theorem oracle_data (board : Board) (boxes holes : Pattern) (hero : Cell)
    (dir : Dir) (outcome : Outcome)
    (checked : stepOracle board boxes holes hero dir = some outcome) :
    ∃ target, advance board hero dir = some target ∧ target ∈ board.floor ∧
      target ∉ board.doors ∧ corner board boxes hero dir = false ∧
      ((boxes target = false ∧ holes target = false ∧ outcome = .walk target) ∨
       (boxes target = true ∧ ∃ ending, pushOracle board boxes holes target dir = some ending ∧
         outcome = .push target ending)) := by
  cases standing : boxes hero || holes hero with
  | true => simp [stepOracle, standing] at checked
  | false =>
    cases adjacent : advance board hero dir with
    | none => simp [stepOracle, standing, adjacent] at checked
    | some target =>
      simp [stepOracle, standing, adjacent] at checked
      obtain ⟨⟨⟨floor,door⟩,clear⟩,checked⟩ := checked
      refine ⟨target, rfl, floor, door, clear, ?_⟩
      cases owner : boxes target with
      | false =>
        cases hazard : holes target with
        | true => simp [owner,hazard] at checked
        | false =>
          simp [owner,hazard] at checked
          exact Or.inl ⟨rfl,rfl,checked.symm⟩
      | true =>
        cases pushed : pushOracle board boxes holes target dir with
        | none => simp [owner,pushed] at checked
        | some ending =>
          simp [owner,pushed] at checked
          exact Or.inr ⟨rfl,ending,rfl,checked.symm⟩

theorem reverse_checked : Geometry.reverseCheck soko1_1.board = true := by decide +kernel

theorem zero_oracle_complete (i : Nat) (checked : nodeCheck i = true)
    (hero : Cell) (inside : hero ∈ region i) (floor : hero ∈ soko1_1.board.floor)
    (dir : Dir) (outcome : Outcome)
    (oracle : stepOracle soko1_1.board (project [cell i]) (project soko1_1.initial.holes)
      hero dir = some outcome)
    (zero : singleSlack hero (cell i) outcome = 0) : Next i outcome := by
  obtain ⟨target, adjacent, targetFloor, door, clear, walked | pushed⟩ :=
    oracle_data _ _ _ _ _ _ oracle
  · obtain ⟨boxClear,holeClear,rfl⟩ := walked
    have different : target ≠ cell i := by
      intro same
      subst target
      simp [project] at boxClear
    have notHole : target ∉ soko1_1.initial.holes := by simpa [project] using holeClear
    exact walk_sound i checked hero inside dir target adjacent targetFloor door different notHole clear
  · obtain ⟨boxPresent,ending,push,rfl⟩ := pushed
    have member : target ∈ [cell i] := List.contains_iff_mem.mp boxPresent
    have same : target = cell i := by simpa using member
    subst target
    have behind := Geometry.reverseCheck_sound soko1_1.board reverse_checked hero floor dir (cell i) adjacent
    have empty := HazardPhases.push_empty_covers soko1_1.board (project [cell i])
      (project soko1_1.initial.holes) (cell i) dir ending push
    exact push_sound i checked hero inside dir ending behind empty zero

/-- Single-token local completeness before the first fill; no multi-token state table. -/
theorem real_zero_complete (i : Nat) (numeric : nodeCheck i = true)
    {state : State} {dir : Dir} {t : Transition} {outcome : Outcome}
    (unique : state.boulders.Nodup) (present : cell i ∈ state.boulders)
    (disjoint : ∀ box ∈ state.boulders, box ∉ state.holes)
    (holes : state.holes = soko1_1.initial.holes)
    (checked : step soko1_1.board state dir = some t) (effect : Matches state t outcome)
    (inside : state.player ∈ region i)
    (zero : singleSlack state.player (cell i) (GhostProjection.projectedOutcome [cell i] outcome) = 0) :
    Next i (GhostProjection.projectedOutcome [cell i] outcome) := by
  have subset : [cell i] ⊆ state.boulders := by simpa using present
  have oracle := GhostProjection.original_matches_shadow soko1_1.board state [cell i]
    unique subset disjoint dir t checked outcome effect
  rw [holes] at oracle
  exact zero_oracle_complete i numeric state.player inside (step_player_clear _ _ _ _ checked).1 dir
    (GhostProjection.projectedOutcome [cell i] outcome) oracle zero

theorem crates_disjoint0 :
    (NetHack.SokobanLinearPhases.Map11.crates 0).all
      (fun box => decide (box ∉ soko1_1.initial.holes)) = true := by decide +kernel

theorem reached_data {state : State} {history : List Dir} {pushes moves : Nat}
    (reached : Trace soko1_1.board soko1_1.initial history state pushes moves)
    (holes : state.holes = soko1_1.initial.holes) :
    state.boulders.Nodup ∧ ∀ box ∈ state.boulders, box ∉ state.holes := by
  have good := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
  refine ⟨good.1, ?_⟩
  obtain ⟨phase, atIndex⟩ := good.2
  have bounded : phase ≤ 16 := atIndex.1
  have lengths := congrArg List.length atIndex.2.1
  simp only [List.length_drop] at lengths
  have currentLength : state.holes.length = 16 := by rw [holes]; rfl
  change state.holes.length = 16 - phase at lengths
  have phaseZero : phase = 0 := by omega
  subst phase
  intro box member
  have inside := atIndex.2.2.2 member
  have numeric := List.all_eq_true.mp crates_disjoint0 box inside
  rw [holes]
  exact of_decide_eq_true numeric

theorem real_zero_from_reached (i : Nat) (active : i < 28)
    {state : State} {history : List Dir} {previousPushes previousMoves : Nat}
    {dir : Dir} {t : Transition} {outcome : Outcome}
    (reached : Trace soko1_1.board soko1_1.initial history state previousPushes previousMoves)
    (present : cell i ∈ state.boulders) (holes : state.holes = soko1_1.initial.holes)
    (checked : step soko1_1.board state dir = some t) (effect : Matches state t outcome)
    (inside : state.player ∈ region i)
    (zero : singleSlack state.player (cell i) (GhostProjection.projectedOutcome [cell i] outcome) = 0) :
    Next i (GhostProjection.projectedOutcome [cell i] outcome) := by
  have facts := reached_data reached holes
  exact real_zero_complete i (all_nodes i active) facts.1 present facts.2 holes checked effect inside zero

#print axioms all_nodes
#print axioms real_zero_from_reached
end Owner1007.ZeroWord11
