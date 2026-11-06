/- Exact inventory of forgotten boulders, classified by any cell property.
These lemmas keep the original Model and all its individual actions. They
justify count/source guards for a proposed weighted projection, not an
optimality theorem or an unproved walking quotient. -/
import NetHack.Sokoban.PatternMass

namespace NetHack.Sokoban.ClassInventory
open LowerBounds HazardPattern

def marked (tracked : List Cell) (classify : Cell → Nat) (kind : Nat) (c : Cell) : Bool :=
  !tracked.contains c && decide (classify c = kind)

def indicator (mark : Cell → Bool) (c : Cell) : Int := if mark c then 1 else 0

def count (tracked : List Cell) (classify : Cell → Nat) (kind : Nat) (boxes : List Cell) : Nat :=
  (boxes.filter (marked tracked classify kind)).length

def value (tracked : List Cell) (classify : Cell → Nat) (kind : Nat) (state : State) : Int :=
  weightSum (indicator (marked tracked classify kind)) state.boulders

theorem indicator_sum (mark : Cell → Bool) (boxes : List Cell) :
    weightSum (indicator mark) boxes = Int.ofNat (boxes.filter mark).length := by
  induction boxes with
  | nil => rfl
  | cons c tail ih =>
    cases selected : mark c <;> simp [indicator, weightSum, selected, ih] <;> omega

theorem value_eq_count (tracked : List Cell) (classify : Cell → Nat) (kind : Nat) (state : State) :
    value tracked classify kind state = Int.ofNat (count tracked classify kind state.boulders) :=
  indicator_sum _ _

def delta (tracked : List Cell) (classify : Cell → Nat) (kind : Nat) : Outcome → Int
  | .walk _ => 0
  | .push source (.stay landing) =>
      indicator (marked tracked classify kind) landing - indicator (marked tracked classify kind) source
  | .push source (.fill _) => -indicator (marked tracked classify kind) source

/-- Exact consumption/transfer of each weight class, for every real effect. -/
theorem matches_delta (tracked : List Cell) (classify : Cell → Nat) (kind : Nat)
    (state : State) (t : Transition) (outcome : Outcome) (effect : Matches state t outcome) :
    value tracked classify kind state + delta tracked classify kind outcome =
      value tracked classify kind t.state := by
  cases outcome with
  | walk target => cases effect; simp [value, delta]
  | push source ending =>
    cases ending with
    | stay landing =>
      rcases effect with ⟨present,shape⟩
      have erased := weightSum_erase (indicator (marked tracked classify kind)) state.boulders source present
      subst t
      simp only [value,delta,weightSum]
      omega
    | fill hole =>
      rcases effect with ⟨present,_,shape⟩
      have erased := weightSum_erase (indicator (marked tracked classify kind)) state.boulders source present
      subst t
      simp only [value,delta]
      omega

theorem count_le_capacity (tracked : List Cell) (classify : Cell → Nat) (kind : Nat)
    (boxes allowed : List Cell) (unique : boxes.Nodup) (within : boxes ⊆ allowed) :
    count tracked classify kind boxes ≤ count tracked classify kind allowed := by
  apply List.Nodup.length_le_of_subset (unique.filter _)
  intro c member
  rcases List.mem_filter.mp member with ⟨present,selected⟩
  exact List.mem_filter.mpr ⟨within present,selected⟩

theorem source_available (tracked : List Cell) (classify : Cell → Nat) (boxes : List Cell)
    (source : Cell) (present : source ∈ boxes) (unknown : source ∉ tracked) :
    0 < count tracked classify (classify source) boxes := by
  apply List.length_pos_of_mem (a := source)
  apply List.mem_filter.mpr
  exact ⟨present,by simp [marked, unknown]⟩

theorem erase_capacity (tracked : List Cell) (classify : Cell → Nat) (kind : Nat)
    (boxes allowed : List Cell) (source : Cell) (unique : boxes.Nodup) (within : boxes ⊆ allowed) :
    count tracked classify kind (boxes.erase source) ≤ count tracked classify kind (allowed.erase source) := by
  apply count_le_capacity tracked classify kind _ _ (unique.erase source)
  intro c member
  have different : c ≠ source := by
    intro same
    subst c
    exact (List.Nodup.not_mem_erase unique) member
  exact (List.mem_erase_of_ne different).mpr (within (List.mem_of_mem_erase member))

theorem clear_capacity (tracked : List Cell) (classify : Cell → Nat) (kind : Nat)
    (boxes allowed clear : List Cell) (unique : boxes.Nodup) (within : boxes ⊆ allowed)
    (cleared : ∀ c ∈ clear, c ∉ boxes) :
    count tracked classify kind boxes ≤
      count tracked classify kind (allowed.filter (fun c => !clear.contains c)) := by
  apply count_le_capacity tracked classify kind _ _ unique
  intro c member
  apply List.mem_filter.mpr
  refine ⟨within member,?_⟩
  have outside : c ∉ clear := fun h => cleared c h member
  simp [outside]

theorem capacity_partition (tracked : List Cell) (classify : Cell → Nat) (kind : Nat)
    (allowed clear : List Cell) :
    count tracked classify kind allowed =
      count tracked classify kind (allowed.filter (fun c => !clear.contains c)) +
      count tracked classify kind (allowed.filter clear.contains) := by
  induction allowed with
  | nil => rfl
  | cons c tail ih =>
    cases selected : marked tracked classify kind c <;>
      cases removed : clear.contains c <;>
      simp only [count,List.filter_cons,selected,removed,Bool.not_true,Bool.not_false,
        Bool.false_eq_true,↓reduceIte,List.length_cons] at ih ⊢ <;> omega

/-- Every collection of cells that a real action clears consumes distinct
capacity from the appropriate classes. This is a necessary, not sufficient,
condition for any proposed projected action. -/
theorem clear_capacity_add (tracked : List Cell) (classify : Cell → Nat) (kind : Nat)
    (boxes allowed clear : List Cell) (unique : boxes.Nodup) (within : boxes ⊆ allowed)
    (cleared : ∀ c ∈ clear, c ∉ boxes) :
    count tracked classify kind boxes + count tracked classify kind (allowed.filter clear.contains) ≤
      count tracked classify kind allowed := by
  have bound := clear_capacity tracked classify kind boxes allowed clear unique within cleared
  have partition := capacity_partition tracked classify kind allowed clear
  omega

theorem full_class_occupied (tracked : List Cell) (classify : Cell → Nat)
    (boxes allowed : List Cell) (c : Cell) (unique : boxes.Nodup) (within : boxes ⊆ allowed)
    (present : c ∈ allowed) (unknown : c ∉ tracked)
    (full : count tracked classify (classify c) boxes = count tracked classify (classify c) allowed) :
    c ∈ boxes := by
  by_cases found : c ∈ boxes
  · exact found
  · have without : boxes ⊆ allowed.erase c := by
      intro x member
      have different : x ≠ c := by intro same; subst x; exact found member
      exact (List.mem_erase_of_ne different).mpr (within member)
    have bound := count_le_capacity tracked classify (classify c) boxes (allowed.erase c) unique without
    have erased := weightSum_erase (indicator (marked tracked classify (classify c))) allowed c present
    have one : indicator (marked tracked classify (classify c)) c = 1 := by
      simp [indicator,marked,unknown]
    rw [indicator_sum,indicator_sum,one] at erased
    change Int.ofNat (count tracked classify (classify c) allowed) =
      1 + Int.ofNat (count tracked classify (classify c) (allowed.erase c)) at erased
    simp only [Int.ofNat_eq_natCast] at erased
    rw [full] at bound
    omega

/-- Source plus any independently proved clearances can be excluded from
the residual capacity. The clearance premise is explicit and not a new
restriction on Model traces. A concrete oracle certificate must derive it. -/
theorem avoiding_capacity (tracked : List Cell) (classify : Cell → Nat) (kind : Nat)
    (boxes allowed clear : List Cell) (source : Cell) (unique : boxes.Nodup)
    (within : boxes ⊆ allowed) (cleared : ∀ c ∈ clear, c ∉ boxes) :
    count tracked classify kind (boxes.erase source) ≤
      count tracked classify kind ((allowed.erase source).filter (fun c => !clear.contains c)) := by
  apply count_le_capacity tracked classify kind _ _ (unique.erase source)
  intro c member
  have original := List.mem_of_mem_erase member
  have different : c ≠ source := by
    intro same
    subst c
    exact (List.Nodup.not_mem_erase unique) member
  apply List.mem_filter.mpr
  refine ⟨(List.mem_erase_of_ne different).mpr (within original),?_⟩
  have outside : c ∉ clear := fun h => cleared c h original
  simp [outside]

/-- Every original individual Model action has the exact inventory update.
Rolling and boulder consumption are inherited through Matches. -/
theorem model_step (tracked : List Cell) (classify : Cell → Nat) (board : Board)
    (state : State) (unique : state.boulders.Nodup) (direction : Dir) (t : Transition)
    (checked : step board state direction = some t) :
    ∃ outcome, stepOracle board (PatternCorrection.project state.boulders)
        (PatternCorrection.project state.holes) state.player direction = some outcome ∧
      Matches state t outcome ∧
      ∀ kind, value tracked classify kind state + delta tracked classify kind outcome =
        value tracked classify kind t.state := by
  rcases stepOracle_covers board state unique direction t checked with ⟨outcome,oracle,effect⟩
  exact ⟨outcome,oracle,effect,fun kind => matches_delta tracked classify kind state t outcome effect⟩

end NetHack.Sokoban.ClassInventory
