/- A guarded certificate reader, not a change to Model or its action set.
Root blocks determine variable order. Interval/rank failures select a literal
inside the proposed interval. Thus ordering and interval soundness follow
for ALL raw data, without trusting a proposer or checking a million separate
ordering rows. Numerical puzzle certificates still need every transition,
initial-value and terminal inequality checked by the ordinary kernel. -/
import NetHack.Sokoban.DecisionDAGBounds
import NetHack.Sokoban.DecisionDAGTransform

namespace NetHack.Sokoban.RankedDAG
open DecisionDAG DecisionDAGTransform

structure Entry where
  low : Nat
  high : Nat
  lower : Nat
  upper : Nat
  deriving DecidableEq, Repr

structure Config where
  stride : Nat
  count : Nat
  label : Nat → Cell
  raw : Nat → Entry

def bounds (cfg : Config) (root : Nat) : DecisionDAGBounds.Interval :=
  if root < 5 then ⟨Int.ofNat root, Int.ofNat root⟩
  else if 0 < root / cfg.stride ∧ root / cfg.stride ≤ cfg.count then
    ⟨Int.ofNat (cfg.raw root).lower, Int.ofNat (max (cfg.raw root).lower (cfg.raw root).upper)⟩
  else ⟨0, 0⟩

def edgeCheck (cfg : Config) (root : Nat) (entry : Entry) : Bool :=
  decide (entry.low < root / cfg.stride * cfg.stride ∧
    entry.high < root / cfg.stride * cfg.stride ∧
    (bounds cfg root).lower ≤ (bounds cfg entry.low).lower ∧
    (bounds cfg root).lower ≤ (bounds cfg entry.high).lower ∧
    (bounds cfg entry.low).upper ≤ (bounds cfg root).upper ∧
    (bounds cfg entry.high).upper ≤ (bounds cfg root).upper)

def read (cfg : Config) (root : Nat) : Node :=
  if root < 5 then .literal (Int.ofNat root)
  else if 0 < root / cfg.stride ∧ root / cfg.stride ≤ cfg.count then
    let entry := cfg.raw root
    if edgeCheck cfg root entry then
      .branch (cfg.label (cfg.count - root / cfg.stride)) entry.low entry.high
    else .literal (bounds cfg root).lower
  else .literal 0

theorem bounds_consistent (cfg : Config) (root : Nat) :
    (bounds cfg root).lower ≤ (bounds cfg root).upper := by
  unfold bounds
  split
  · exact Int.le_refl _
  · split
    · exact Int.ofNat_le.mpr (Nat.le_max_left _ _)
    · exact Int.le_refl _

theorem bounds_nonnegative (cfg : Config) (root : Nat) : 0 ≤ (bounds cfg root).lower := by
  unfold bounds
  split
  · exact Int.natCast_nonneg _
  · split
    · exact Int.natCast_nonneg _
    · exact Int.le_refl _

theorem branch_facts (cfg : Config) (root cell low high : Nat)
    (code : read cfg root = .branch cell low high) :
    0 < root / cfg.stride ∧ root / cfg.stride ≤ cfg.count ∧
    cell = cfg.label (cfg.count - root / cfg.stride) ∧
    low = (cfg.raw root).low ∧ high = (cfg.raw root).high ∧
    edgeCheck cfg root (cfg.raw root) = true := by
  by_cases small : root < 5
  · simp only [read, if_pos small] at code
    cases code
  · by_cases active : 0 < root / cfg.stride ∧ root / cfg.stride ≤ cfg.count
    · simp only [read, if_neg small, if_pos active] at code
      cases checked : edgeCheck cfg root (cfg.raw root) with
      | false => simp only [checked, Bool.false_eq_true, ↓reduceIte] at code; cases code
      | true =>
        simp only [checked, ↓reduceIte] at code
        cases code
        exact ⟨active.1, active.2, rfl, rfl, rfl, rfl⟩
    · simp only [read, if_neg small, if_neg active] at code
      cases code

theorem literal_bounded (cfg : Config) (root : Nat) (value : Int)
    (code : read cfg root = .literal value) :
    (bounds cfg root).lower ≤ value ∧ value ≤ (bounds cfg root).upper := by
  by_cases small : root < 5
  · simp only [read, if_pos small] at code
    cases code
    simp only [bounds, if_pos small]
    exact ⟨Int.le_refl _, Int.le_refl _⟩
  · by_cases active : 0 < root / cfg.stride ∧ root / cfg.stride ≤ cfg.count
    · simp only [read, if_neg small, if_pos active] at code
      cases checked : edgeCheck cfg root (cfg.raw root) with
      | false =>
        simp only [checked, Bool.false_eq_true, ↓reduceIte] at code
        cases code
        exact ⟨Int.le_refl _, bounds_consistent cfg root⟩
      | true => simp only [checked, ↓reduceIte] at code; cases code
    · simp only [read, if_neg small, if_neg active] at code
      cases code
      simp only [bounds, if_neg small, if_neg active]
      exact ⟨Int.le_refl _, Int.le_refl _⟩

theorem all_bounds_checks (cfg : Config) (root : Nat) :
    DecisionDAGBounds.check (read cfg) (bounds cfg) root = true := by
  cases code : read cfg root with
  | literal value =>
    simpa only [DecisionDAGBounds.check, code, decide_eq_true_eq] using
      literal_bounded cfg root value code
  | branch cell low high =>
    have facts := branch_facts cfg root cell low high code
    have limits := of_decide_eq_true facts.2.2.2.2.2
    have base := Nat.div_mul_le_self root cfg.stride
    have edges : low < root ∧ high < root := by
      rw [facts.2.2.2.1, facts.2.2.2.2.1]
      exact ⟨Nat.lt_of_lt_of_le limits.1 base, Nat.lt_of_lt_of_le limits.2.1 base⟩
    simp only [DecisionDAGBounds.check, code, if_pos edges, decide_eq_true_eq]
    simpa only [facts.2.2.2.1, facts.2.2.2.2.1] using limits.2.2

theorem eval_bounded (cfg : Config) (p : Pattern) (root : Nat) :
    (bounds cfg root).lower ≤ eval (read cfg) p root ∧
      eval (read cfg) p root ≤ (bounds cfg root).upper :=
  DecisionDAGBounds.checked_sound (read cfg) (bounds cfg) (all_bounds_checks cfg) p root

theorem eval_nonnegative (cfg : Config) (p : Pattern) (root : Nat) :
    0 ≤ eval (read cfg) p root :=
  Int.le_trans (bounds_nonnegative cfg root) (eval_bounded cfg p root).1

theorem reader_supported (cfg : Config) :
    Supported (read cfg) ((List.range cfg.count).map cfg.label) := by
  intro root cell low high code
  have facts := branch_facts cfg root cell low high code
  apply List.mem_map.mpr
  refine ⟨cfg.count - root / cfg.stride, List.mem_range.mpr (by omega), facts.2.2.1.symm⟩

theorem reader_ordered (cfg : Config) (positive : 0 < cfg.stride)
    (labels : ∀ i j, i < cfg.count → j < cfg.count → i < j → cfg.label i < cfg.label j) :
    Ordered (read cfg) := by
  intro root cell low high code
  have facts := branch_facts cfg root cell low high code
  have limits := of_decide_eq_true facts.2.2.2.2.2
  have childAbove (child : Nat) (earlier : child < root / cfg.stride * cfg.stride) :
      Above (read cfg) child (cell + 1) := by
    intro childCell left right childCode
    have childFacts := branch_facts cfg child childCell left right childCode
    have level : child / cfg.stride < root / cfg.stride :=
      (Nat.div_lt_iff_lt_mul positive).mpr earlier
    have smaller : cfg.count - root / cfg.stride < cfg.count - child / cfg.stride := by omega
    have increasing := labels (cfg.count - root / cfg.stride) (cfg.count - child / cfg.stride)
      (by omega) (by omega) smaller
    rw [facts.2.2.1, childFacts.2.2.1]
    exact Nat.succ_le_of_lt increasing
  exact ⟨childAbove low (facts.2.2.2.1 ▸ limits.1),
    childAbove high (facts.2.2.2.2.1 ▸ limits.2.1)⟩

end NetHack.Sokoban.RankedDAG
