/- Removing boulders is a relaxation of successful collision-free actions.
This generic lemma retains the first hazard, rolling endpoint, doors and
NetHack's diagonal-corner rule. It supplies no numerical map bound. -/
import NetHack.Sokoban.HazardPhases
import NetHack.Sokoban.PatternMass
import NetHack.Sokoban.HazardPhaseCountedCorrection
set_option linter.unusedSimpArgs false
namespace NetHack.Sokoban.ProjectedOracle
open PatternCorrection HazardPattern

def Included (small large : Pattern) : Prop := ∀ cell, small cell = true → large cell = true

theorem clear_of_included {small large : Pattern} (included : Included small large)
    (cell : Cell) (clear : large cell = false) : small cell = false := by
  cases selected : small cell with
  | false => rfl
  | true => have := included cell selected; rw [clear] at this; contradiction

theorem erase_included {small large : Pattern} (included : Included small large)
    (source : Cell) : Included (change small source none) (change large source none) := by
  intro cell selected
  by_cases same : source = cell
  · simp [change,same] at selected
  · simpa [change,same] using included cell (by simpa [change,same] using selected)

theorem roll_covers (board : Board) {small large : Pattern} (included : Included small large)
    (holes : Pattern) (direction : Dir) (fuel current : Nat) (result : Ending)
    (checked : rollOracle board large holes direction fuel current = some result) :
    rollOracle board small holes direction fuel current = some result := by
  induction fuel generalizing current with
  | zero => simp [rollOracle] at checked
  | succ fuel ih =>
    cases adjacent : advance board current direction with
    | none => simpa [rollOracle,adjacent] using checked
    | some next =>
      cases door : board.doors.contains next <;> cases floor : board.floor.contains next <;>
        simp only [rollOracle,adjacent,door,floor,Bool.not_true,Bool.not_false,
          Bool.false_eq_true,↓reduceIte] at checked ⊢
      all_goals first | contradiction | exact checked | skip
      cases box : large next with
      | true => simp [box] at checked
      | false =>
        have smallClear := clear_of_included included next box
        cases hole : holes next <;>
          simp only [box,smallClear,hole,Bool.false_eq_true,↓reduceIte] at checked ⊢
        · exact ih next checked
        · exact checked

theorem push_covers (board : Board) {small large : Pattern} (included : Included small large)
    (holes : Pattern) (source : Cell) (direction : Dir) (result : Ending)
    (checked : pushOracle board large holes source direction = some result) :
    pushOracle board small holes source direction = some result := by
  cases diagonal : direction.diagonal with
  | true => simp [pushOracle,diagonal] at checked
  | false =>
    cases behind : advance board source direction.opposite with
    | none => simp [pushOracle,diagonal,behind] at checked
    | some cell =>
      cases supportFloor : board.floor.contains cell <;> cases supportDoor : board.doors.contains cell <;>
        simp only [pushOracle,diagonal,Bool.false_eq_true,↓reduceIte,bind,pure,
          Option.bind_some,behind,supportFloor,supportDoor,Bool.not_true,Bool.not_false,
          Bool.false_or,Bool.true_or] at checked ⊢
      all_goals first | contradiction | skip
      cases destination : advance board source direction with
      | none => simp [destination] at checked
      | some first =>
        cases floor : board.floor.contains first <;> cases door : board.doors.contains first <;>
          simp only [destination,Option.bind_some,floor,door,Bool.not_true,Bool.not_false,
            Bool.false_or,Bool.true_or,Bool.false_eq_true,↓reduceIte] at checked ⊢
        all_goals first | contradiction | skip
        cases box : large first with
        | true => simp [box] at checked
        | false =>
          have smallClear := clear_of_included included first box
          cases hole : holes first <;> cases rolling : board.rollingTraps.contains first <;>
            simp only [box,smallClear,hole,rolling,Bool.false_or,Bool.false_eq_true,↓reduceIte] at checked ⊢
          all_goals first | exact checked | exact roll_covers board (erase_included included source) holes direction _ source result checked

/-- Definitionally the same side predicate as HazardPattern's private helper. -/
def side (board : Board) (boxes : Pattern) (hero : Cell) (direction : Dir) : Bool :=
  match advance board hero direction with
  | none => true
  | some cell => (!board.floor.contains cell && !board.doors.contains cell) || boxes cell

theorem side_mono (board : Board) {small large : Pattern} (included : Included small large)
    (hero : Cell) (direction : Dir) (blocked : side board small hero direction = true) :
    side board large hero direction = true := by
  cases adjacent : advance board hero direction with
  | none => simp [side,adjacent]
  | some cell =>
    simp only [side,adjacent] at blocked ⊢
    cases fixed : (!board.floor.contains cell && !board.doors.contains cell) with
    | false => simpa only [fixed,Bool.false_or] using included cell (by simpa only [fixed,Bool.false_or] using blocked)
    | true => simp [fixed]

theorem corner_mono (board : Board) {small large : Pattern} (included : Included small large)
    (hero : Cell) (direction : Dir) (blocked : corner board small hero direction = true) :
    corner board large hero direction = true := by
  change (direction.diagonal && side board small hero direction.sides.1 &&
    side board small hero direction.sides.2) = true at blocked
  change (direction.diagonal && side board large hero direction.sides.1 &&
    side board large hero direction.sides.2) = true
  rcases Bool.and_eq_true_iff.mp blocked with ⟨first,second⟩
  rcases Bool.and_eq_true_iff.mp first with ⟨diagonal,first⟩
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨diagonal,side_mono board included hero _ first⟩,
    side_mono board included hero _ second⟩

theorem corner_clear (board : Board) {small large : Pattern} (included : Included small large)
    (hero : Cell) (direction : Dir) (clear : corner board large hero direction = false) :
    corner board small hero direction = false := by
  cases selected : corner board small hero direction with
  | false => rfl
  | true => have := corner_mono board included hero direction selected; rw [clear] at this; contradiction

/-- A successful action is preserved under obstacle removal when the occupancy
of the adjacent target is retained. This prevents replacing a push by a walk. -/
theorem step_covers (board : Board) {small large : Pattern} (included : Included small large)
    (holes : Pattern) (hero : Cell) (direction : Dir)
    (targetSame : ∀ target, advance board hero direction = some target → small target = large target)
    (outcome : Outcome) (checked : stepOracle board large holes hero direction = some outcome) :
    stepOracle board small holes hero direction = some outcome := by
  cases heroBox : large hero with
  | true => simp [stepOracle,heroBox] at checked
  | false =>
    have smallHero := clear_of_included included hero heroBox
    cases heroHole : holes hero with
    | true => simp [stepOracle,heroBox,heroHole] at checked
    | false =>
      cases adjacent : advance board hero direction with
      | none => simp [stepOracle,heroBox,heroHole,adjacent] at checked
      | some target =>
        cases floor : board.floor.contains target <;> cases door : board.doors.contains target <;>
          cases largeCorner : corner board large hero direction <;>
          simp only [stepOracle,heroBox,heroHole,adjacent,floor,door,largeCorner,
            Bool.false_or,Bool.true_or,Bool.not_true,Bool.not_false,Bool.false_eq_true,
            ↓reduceIte,bind,pure,Option.bind_some,Option.bind_none] at checked
        all_goals first | contradiction | skip
        have smallCorner := corner_clear board included hero direction largeCorner
        have same := targetSame target adjacent
        cases targetBox : large target with
        | false =>
          cases targetHole : holes target <;>
            simp only [stepOracle,heroBox,smallHero,heroHole,adjacent,floor,door,
              largeCorner,smallCorner,same,targetBox,targetHole,Bool.false_or,
              Bool.true_or,Bool.not_true,Bool.not_false,Bool.false_eq_true,
              ↓reduceIte,bind,pure,Option.bind_some,Option.bind_none] at checked ⊢
          all_goals first | contradiction | exact checked
        | true =>
          cases pushed : pushOracle board large holes target direction with
          | none => simp [targetBox,pushed] at checked
          | some result =>
            have smallPush := push_covers board included holes target direction result pushed
            simpa only [stepOracle,heroBox,smallHero,heroHole,adjacent,floor,door,
              largeCorner,smallCorner,same,targetBox,pushed,smallPush,Bool.false_or,
              Bool.true_or,Bool.not_true,Bool.not_false,Bool.false_eq_true,
              ↓reduceIte,bind,pure,Option.bind_some,Option.bind_none] using checked

def force (pattern : Pattern) (source : Cell) : Pattern :=
  fun cell => if cell = source then true else pattern cell

theorem selected_included (cells : List Cell) (large : Pattern) :
    Included (boxes cells large) large := by
  intro cell present
  exact (Bool.and_eq_true_iff.mp present).2

theorem force_included {small large : Pattern} (included : Included small large)
    (source : Cell) (occupied : large source = true) : Included (force small source) large := by
  intro cell selected
  by_cases same : cell = source
  · simpa only [same] using occupied
  · exact included cell (by simpa [force,same] using selected)

/-- The second action may use one available untracked boulder. It is not an
infinite supply: availability is a separate cardinality obligation. -/
def choices (board : Board) (cells : List Cell) (ghost : Bool) (known holes : Pattern)
    (hero : Cell) (direction : Dir) : List Outcome :=
  (stepOracle board known holes hero direction).toList ++
    match advance board hero direction with
    | none => []
    | some source =>
      if ghost && !cells.contains source then
        (stepOracle board (force known source) holes hero direction).toList else []

theorem choices_covers (board : Board) (cells : List Cell) (ghost : Bool)
    (large holes : Pattern) (hero : Cell) (direction : Dir)
    (available : ∀ cell, cell ∉ cells → large cell = true → ghost = true)
    (outcome : Outcome) (checked : stepOracle board large holes hero direction = some outcome) :
    outcome ∈ choices board cells ghost (boxes cells large) holes hero direction := by
  have included := selected_included cells large
  cases adjacent : advance board hero direction with
  | none =>
    cases blocked : large hero || holes hero <;> simp [stepOracle,blocked,adjacent] at checked
  | some target =>
    have sameTarget (small : Pattern) (same : small target = large target) :
        ∀ other, advance board hero direction = some other → small other = large other := by
      intro other second
      have eq := Option.some.inj (adjacent.symm.trans second)
      subst other
      exact same
    by_cases tracked : target ∈ cells
    · have same : boxes cells large target = large target := by simp [boxes,tracked]
      have kept := step_covers board included holes hero direction (sameTarget _ same) outcome checked
      unfold choices
      apply List.mem_append.mpr
      left
      simp [kept]
    · cases occupied : large target with
      | false =>
        have same : boxes cells large target = large target :=
          (clear_of_included included target occupied).trans occupied.symm
        have kept := step_covers board included holes hero direction (sameTarget _ same) outcome checked
        unfold choices
        apply List.mem_append.mpr
        left
        simp [kept]
      | true =>
        have supplied := available target tracked occupied
        have includedForce := force_included included target occupied
        have same : force (boxes cells large) target target = large target := by simp [force,occupied]
        have kept := step_covers board includedForce holes hero direction (sameTarget _ same) outcome checked
        have absent : cells.contains target = false := by simp [tracked]
        simp only [choices,adjacent,supplied,absent,Bool.not_false,Bool.true_and,↓reduceIte]
        apply List.mem_append.mpr
        right
        simp [kept]

theorem selected_mass (cells : List Cell) (large : Pattern) :
    PatternMass.mass cells (boxes cells large) = PatternMass.mass cells large := by
  unfold PatternMass.mass
  apply congrArg List.length
  apply List.filter_congr
  intro cell member
  simp [boxes,member]

theorem availability_of_mass (allowedCells cells : List Cell) (large : Pattern) (total : Nat)
    (unique : cells.Nodup) (subset : cells ⊆ allowedCells)
    (supported : ∀ cell, large cell = true → cell ∈ allowedCells)
    (budget : PatternMass.mass allowedCells large ≤ total) :
    ∀ cell, cell ∉ cells → large cell = true → decide (PatternMass.mass cells large < total) = true := by
  intro cell forgotten occupied
  have extra := PatternMass.mass_extra cells allowedCells large unique subset cell
    (supported cell occupied) occupied forgotten
  exact decide_eq_true (by omega)

/-- An executable projection with a finite remaining-boulder budget. -/
def projectedChoices (board : Board) (cells : List Cell) (total : Nat)
    (large holes : Pattern) (hero : Cell) (direction : Dir) : List Outcome :=
  let known := boxes cells large
  choices board cells (decide (PatternMass.mass cells known < total)) known holes hero direction

theorem projected_covers (board : Board) (allowedCells cells : List Cell) (total : Nat)
    (large holes : Pattern) (hero : Cell) (direction : Dir)
    (unique : cells.Nodup) (subset : cells ⊆ allowedCells)
    (supported : ∀ cell, large cell = true → cell ∈ allowedCells)
    (budget : PatternMass.mass allowedCells large ≤ total)
    (outcome : Outcome) (checked : stepOracle board large holes hero direction = some outcome) :
    outcome ∈ projectedChoices board cells total large holes hero direction := by
  unfold projectedChoices
  apply choices_covers board cells _ large holes hero direction _ outcome checked
  rw [selected_mass]
  exact availability_of_mass allowedCells cells large total unique subset supported budget

/-- Covers every successful original Model action, with its exact push/fill
metadata. The support and mass premises are supplied by proved Trace invariants;
there is no assumption about a proposer's reachable states or RNG. -/
theorem model_covers (board : Board) (allowedCells cells : List Cell) (total : Nat)
    (state : State) (direction : Dir) (t : Transition)
    (universeUnique : allowedCells.Nodup) (selectedUnique : cells.Nodup)
    (selectedSubset : cells ⊆ allowedCells) (boxesUnique : state.boulders.Nodup)
    (within : state.boulders ⊆ allowedCells) (budget : state.boulders.length ≤ total)
    (checked : step board state direction = some t) :
    ∃ outcome, outcome ∈ projectedChoices board cells total (project state.boulders)
      (project state.holes) state.player direction ∧ Matches state t outcome := by
  have supported : ∀ cell, project state.boulders cell = true → cell ∈ allowedCells := by
    intro cell occupied
    apply within
    simpa [project] using occupied
  have mass : PatternMass.mass allowedCells (project state.boulders) ≤ total := by
    rw [PatternMass.project_mass allowedCells state.boulders universeUnique boxesUnique within]
    exact budget
  rcases stepOracle_covers board state boxesUnique direction t checked with ⟨outcome,oracle,effect⟩
  exact ⟨outcome,projected_covers board allowedCells cells total (project state.boulders)
    (project state.holes) state.player direction selectedUnique selectedSubset supported mass outcome oracle,effect⟩

theorem selected_after (cells : List Cell) (pattern : Pattern) (outcome : Outcome) :
    boxes cells (HazardPhaseCountedCorrection.afterBoxes pattern outcome) =
      boxes cells (HazardPhaseCountedCorrection.afterBoxes (boxes cells pattern) outcome) := by
  funext cell
  by_cases member : cell ∈ cells
  · cases outcome with
    | walk target => simp [HazardPhaseCountedCorrection.afterBoxes,boxes,member]
    | push source ending => cases ending <;>
        simp [HazardPhaseCountedCorrection.afterBoxes,boxes,change,member]
  · simp [boxes,member]

def projectedAfter (cells : List Cell) (known : Pattern) (outcome : Outcome) : Pattern :=
  boxes cells (HazardPhaseCountedCorrection.afterBoxes known outcome)

theorem matches_selected (cells : List Cell) (state : State) (t : Transition)
    (unique : state.boulders.Nodup) (outcome : Outcome) (effect : Matches state t outcome) :
    boxes cells (project t.state.boulders) = projectedAfter cells (boxes cells (project state.boulders)) outcome := by
  rw [HazardPhaseCountedCorrection.matches_boxes state t unique outcome effect]
  exact selected_after cells (project state.boulders) outcome

/-- The projected action retains the exact original push cost through the
linear-potential delta. No equality with moves/game ticks is assumed. -/
theorem model_covers_reduced (board : Board) (allowedCells cells : List Cell) (total : Nat)
    (potential : LowerBounds.Potential) (state : State) (direction : Dir) (t : Transition)
    (allowedUnique : allowedCells.Nodup) (selectedUnique : cells.Nodup)
    (selectedSubset : cells ⊆ allowedCells) (boxesUnique : state.boulders.Nodup)
    (within : state.boulders ⊆ allowedCells) (budget : state.boulders.length ≤ total)
    (checked : step board state direction = some t) :
    ∃ outcome, outcome ∈ projectedChoices board cells total (project state.boulders)
        (project state.holes) state.player direction ∧ Matches state t outcome ∧
      boxes cells (project t.state.boulders) = projectedAfter cells (boxes cells (project state.boulders)) outcome ∧
      potential.value state + slack potential outcome = Int.ofNat t.pushCost + potential.value t.state := by
  rcases model_covers board allowedCells cells total state direction t allowedUnique
    selectedUnique selectedSubset boxesUnique within budget checked with ⟨outcome,member,effect⟩
  exact ⟨outcome,member,effect,matches_selected cells state t boxesUnique outcome effect,
    matches_delta potential state t outcome effect⟩

def sourceAllowed (allowedCells : List Cell) : Outcome → Bool
  | .walk _ => true
  | .push source _ => allowedCells.contains source

def domainChoices (board : Board) (allowedCells cells : List Cell) (total : Nat)
    (large holes : Pattern) (hero : Cell) (direction : Dir) : List Outcome :=
  (projectedChoices board cells total large holes hero direction).filter (sourceAllowed allowedCells)

theorem matches_source_allowed (allowedCells : List Cell) (state : State) (t : Transition)
    (within : state.boulders ⊆ allowedCells) (outcome : Outcome) (effect : Matches state t outcome) :
    sourceAllowed allowedCells outcome = true := by
  cases outcome with
  | walk target => rfl
  | push source ending =>
    cases ending with
    | stay landing => simpa [sourceAllowed] using within effect.1
    | fill hole => simpa [sourceAllowed] using within effect.1

theorem model_covers_domain (board : Board) (allowedCells cells : List Cell) (total : Nat)
    (potential : LowerBounds.Potential) (state : State) (direction : Dir) (t : Transition)
    (allowedUnique : allowedCells.Nodup) (selectedUnique : cells.Nodup)
    (selectedSubset : cells ⊆ allowedCells) (boxesUnique : state.boulders.Nodup)
    (within : state.boulders ⊆ allowedCells) (budget : state.boulders.length ≤ total)
    (checked : step board state direction = some t) :
    ∃ outcome, outcome ∈ domainChoices board allowedCells cells total (project state.boulders)
        (project state.holes) state.player direction ∧ Matches state t outcome ∧
      boxes cells (project t.state.boulders) = projectedAfter cells (boxes cells (project state.boulders)) outcome ∧
      potential.value state + slack potential outcome = Int.ofNat t.pushCost + potential.value t.state := by
  rcases model_covers_reduced board allowedCells cells total potential state direction t allowedUnique
    selectedUnique selectedSubset boxesUnique within budget checked with ⟨outcome,member,effect,updated,cost⟩
  exact ⟨outcome,List.mem_filter.mpr ⟨member,matches_source_allowed allowedCells state t within outcome effect⟩,
    effect,updated,cost⟩
end NetHack.Sokoban.ProjectedOracle
