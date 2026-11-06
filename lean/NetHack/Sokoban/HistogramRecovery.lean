/- Exact finite histograms recover both the mass and the weight of all
forgotten boulders. The class range is a proved premise, not a discarded
part of a Model state. No search or walking quotient is trusted here. -/
import NetHack.Sokoban.ClassInventory
import NetHack.Sokoban.StatePermutation

namespace NetHack.Sokoban.HistogramRecovery
open LowerBounds ClassInventory

theorem sum_zero (cells : List Cell) : weightSum (fun _ => 0) cells = 0 := by
  induction cells with
  | nil => rfl
  | cons c tail ih => simp only [weightSum, ih, Int.zero_add]

theorem sum_add (f g : Cell → Int) (cells : List Cell) :
    weightSum (fun c => f c + g c) cells = weightSum f cells + weightSum g cells := by
  induction cells with
  | nil => rfl
  | cons c tail ih => simp only [weightSum, ih]; omega

theorem sum_congr (f g : Cell → Int) (cells : List Cell)
    (same : ∀ c ∈ cells, f c = g c) : weightSum f cells = weightSum g cells := by
  induction cells with
  | nil => rfl
  | cons c tail ih =>
    simp only [weightSum]
    rw [same c (by simp), ih (fun x member => same x (by simp [member]))]

theorem sum_single_count (kinds : List Nat) (kind : Nat) (amount : Int) :
    weightSum (fun k => if kind = k then amount else 0) kinds =
      Int.ofNat (kinds.count kind) * amount := by
  induction kinds with
  | nil => simp [weightSum]
  | cons k tail ih =>
    by_cases same : kind = k
    · subst k
      simp only [weightSum, ↓reduceIte, ih, List.count_cons_self,
        Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
      omega
    · simp [weightSum, same, ih, List.count_cons_of_ne (Ne.symm same)]

theorem sum_single (kinds : List Nat) (unique : kinds.Nodup) (kind : Nat)
    (present : kind ∈ kinds) (amount : Int) :
    weightSum (fun k => if kind = k then amount else 0) kinds = amount := by
  rw [sum_single_count, unique.count, if_pos present]
  simp

theorem atom (tracked : List Cell) (classify : Cell → Nat) (coefficient : Nat → Int)
    (kinds : List Nat) (unique : kinds.Nodup) (c : Cell)
    (range : c ∉ tracked → classify c ∈ kinds) :
    weightSum (fun k => coefficient k * indicator (marked tracked classify k) c) kinds =
      if tracked.contains c then 0 else coefficient (classify c) := by
  by_cases known : c ∈ tracked
  · simp [marked, indicator, known, sum_zero]
  · have same : (fun k => coefficient k * indicator (marked tracked classify k) c) =
        (fun k => if classify c = k then coefficient (classify c) else 0) := by
      funext k
      by_cases selected : classify c = k
      · subst k; simp [marked, indicator, known]
      · simp [marked, indicator, known, selected]
    rw [same, sum_single kinds unique (classify c) (range known)]
    simp [known]

/-- A finite exact class histogram loses no forgotten contribution for any
coefficient function, including the signed original potential. -/
theorem weighted_inventory (tracked : List Cell) (classify : Cell → Nat)
    (coefficient : Nat → Int) (kinds : List Nat) (unique : kinds.Nodup)
    (boxes : List Cell) (range : ∀ c ∈ boxes, c ∉ tracked → classify c ∈ kinds) :
    weightSum (fun k => coefficient k *
      weightSum (indicator (marked tracked classify k)) boxes) kinds =
      weightSum (fun c => if tracked.contains c then 0 else coefficient (classify c)) boxes := by
  induction boxes with
  | nil => simp [weightSum, sum_zero]
  | cons c tail ih =>
    simp only [weightSum, Int.mul_add]
    rw [sum_add, atom tracked classify coefficient kinds unique c
      (range c (by simp)), ih (fun x member => range x (by simp [member]))]

theorem count_recovery (tracked : List Cell) (classify : Cell → Nat)
    (kinds : List Nat) (unique : kinds.Nodup) (state : State)
    (range : ∀ c ∈ state.boulders, c ∉ tracked → classify c ∈ kinds) :
    weightSum (fun k => Int.ofNat (count tracked classify k state.boulders)) kinds =
      Int.ofNat ((state.boulders.filter (fun c => !tracked.contains c)).length) := by
  have recover := weighted_inventory tracked classify (fun _ => 1) kinds unique state.boulders range
  simp only [Int.one_mul, indicator_sum] at recover
  unfold count
  rw [recover]
  have same : (fun c => if tracked.contains c then (0 : Int) else 1) =
      indicator (fun c => !tracked.contains c) := by
    funext c
    by_cases known : c ∈ tracked <;> simp [indicator,known]
  rw [same, indicator_sum]

theorem potential_recovery (tracked : List Cell) (classify : Cell → Nat)
    (coefficient : Nat → Int) (kinds : List Nat) (unique : kinds.Nodup)
    (weight : Cell → Int) (state : State)
    (range : ∀ c ∈ state.boulders, c ∉ tracked → classify c ∈ kinds)
    (correct : ∀ c ∈ state.boulders, c ∉ tracked → coefficient (classify c) = weight c) :
    weightSum (fun k => coefficient k * Int.ofNat (count tracked classify k state.boulders)) kinds =
      weightSum (fun c => if tracked.contains c then 0 else weight c) state.boulders := by
  have recover := weighted_inventory tracked classify coefficient kinds unique state.boulders range
  simp only [indicator_sum] at recover
  unfold count
  rw [recover]
  apply sum_congr
  intro c member
  by_cases known : c ∈ tracked
  · simp [known]
  · simp [known, correct c member known]

theorem filter_partition (weight : Cell → Int) (mark : Cell → Bool) (boxes : List Cell) :
    weightSum weight (boxes.filter mark) + weightSum weight (boxes.filter (fun c => !mark c)) =
      weightSum weight boxes := by
  induction boxes with
  | nil => rfl
  | cons c tail ih =>
    cases selected : mark c <;>
      simp only [List.filter_cons, selected, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte, weightSum] <;> omega

theorem filter_zero (weight : Cell → Int) (mark : Cell → Bool) (boxes : List Cell) :
    weightSum (fun c => if mark c then 0 else weight c) boxes =
      weightSum weight (boxes.filter (fun c => !mark c)) := by
  induction boxes with
  | nil => rfl
  | cons c tail ih =>
    cases selected : mark c <;>
      simp only [List.filter_cons, selected, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte, weightSum, ih, Int.zero_add]

theorem filtered_intersection (tracked boxes : List Cell) (trackedUnique : tracked.Nodup)
    (boxesUnique : boxes.Nodup) :
    (boxes.filter tracked.contains).Perm (tracked.filter boxes.contains) := by
  apply (List.perm_ext_iff_of_nodup (boxesUnique.filter _) (trackedUnique.filter _)).mpr
  intro c
  simp [List.mem_filter, and_comm]

/-- Exact total signed weight from the selected occupancy and the histogram.
Both summands are finite projected data; ordered boulder-list representation
does not change the result. -/
theorem full_weight (tracked : List Cell) (classify : Cell → Nat)
    (coefficient : Nat → Int) (kinds : List Nat) (kindsUnique : kinds.Nodup)
    (weight : Cell → Int) (state : State) (trackedUnique : tracked.Nodup)
    (boxesUnique : state.boulders.Nodup)
    (range : ∀ c ∈ state.boulders, c ∉ tracked → classify c ∈ kinds)
    (correct : ∀ c ∈ state.boulders, c ∉ tracked → coefficient (classify c) = weight c) :
    weightSum weight (tracked.filter state.boulders.contains) +
      weightSum (fun k => coefficient k * Int.ofNat (count tracked classify k state.boulders)) kinds =
      weightSum weight state.boulders := by
  rw [potential_recovery tracked classify coefficient kinds kindsUnique weight state range correct,
    filter_zero]
  rw [← StatePermutation.weightSum_permutation weight
    (filtered_intersection tracked state.boulders trackedUnique boxesUnique)]
  exact filter_partition weight tracked.contains state.boulders

theorem mass_partition (mark : Cell → Bool) (boxes : List Cell) :
    (boxes.filter mark).length + (boxes.filter (fun c => !mark c)).length = boxes.length := by
  induction boxes with
  | nil => rfl
  | cons c tail ih =>
    cases selected : mark c <;>
      simp only [List.filter_cons, selected, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

theorem full_mass (tracked : List Cell) (classify : Cell → Nat)
    (kinds : List Nat) (kindsUnique : kinds.Nodup) (state : State)
    (trackedUnique : tracked.Nodup) (boxesUnique : state.boulders.Nodup)
    (range : ∀ c ∈ state.boulders, c ∉ tracked → classify c ∈ kinds) :
    Int.ofNat (tracked.filter state.boulders.contains).length +
      weightSum (fun k => Int.ofNat (count tracked classify k state.boulders)) kinds =
      Int.ofNat state.boulders.length := by
  rw [count_recovery tracked classify kinds kindsUnique state range,
    ← (filtered_intersection tracked state.boulders trackedUnique boxesUnique).length_eq]
  have partition := mass_partition tracked.contains state.boulders
  simp only [Int.ofNat_eq_natCast]
  omega

end NetHack.Sokoban.HistogramRecovery
