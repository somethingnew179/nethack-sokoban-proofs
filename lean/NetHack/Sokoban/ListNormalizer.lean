/- Canonical finite lists for exact-state certificates. Supports are closed
invariants of Model, not smaller maps or assumptions about a searcher. -/
import NetHack.Sokoban.FiniteResidual
import NetHack.Sokoban.ClosedSupport
import NetHack.Sokoban.PatternCorrection

namespace NetHack.Sokoban.ListNormalizer
open StatePermutation FiniteResidual

def Good (cells holes : List Cell) (s : State) : Prop :=
  ClosedSupport.Within cells s ∧ s.boulders.Nodup ∧ s.holes.Nodup ∧ s.holes ⊆ holes
instance (cells holes : List Cell) (s : State) : Decidable (Good cells holes s) := by
  unfold Good; infer_instance

def normalize (cells holes : List Cell) (s : State) : State :=
  ⟨s.player, cells.filter s.boulders.contains, holes.filter s.holes.contains⟩

theorem normalize_equivalent (cells holes : List Cell) (cellsUnique : cells.Nodup)
    (holesUnique : holes.Nodup) (s : State) (good : Good cells holes s) :
    Equivalent s (normalize cells holes s) := by
  refine ⟨rfl, ?_, ?_⟩
  · apply (List.perm_ext_iff_of_nodup good.2.1 (cellsUnique.filter _)).mpr
    intro cell
    simp only [normalize, List.mem_filter, List.contains_iff_mem]
    exact ⟨fun present => ⟨good.1.2 present, present⟩, fun h => h.2⟩
  · apply (List.perm_ext_iff_of_nodup good.2.2.1 (holesUnique.filter _)).mpr
    intro cell
    simp only [normalize, List.mem_filter, List.contains_iff_mem]
    exact ⟨fun present => ⟨good.2.2.2 present, present⟩, fun h => h.2⟩

theorem filter_contains_filter (cells : List Cell) (p : Cell → Bool) :
    cells.filter (cells.filter p).contains = cells.filter p := by
  apply List.filter_congr
  intro c member
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_filter, member, true_and]

theorem normalize_filtered (cells holes : List Cell) (boxes hazards : Cell → Bool) (hero : Cell) :
    normalize cells holes ⟨hero, cells.filter boxes, holes.filter hazards⟩ =
      ⟨hero, cells.filter boxes, holes.filter hazards⟩ := by
  simp only [normalize, filter_contains_filter]

theorem normalize_respects (cells holes : List Cell) (a b : State) (related : Equivalent a b) :
    normalize cells holes a = normalize cells holes b := by
  have boxes : a.boulders.contains = b.boulders.contains := funext fun _ => related.boulders.contains_eq
  have hazards : a.holes.contains = b.holes.contains := funext fun _ => related.holes.contains_eq
  simp only [normalize, related.player, boxes, hazards]

def normalizer (board : Board) (cells holes : List Cell)
    (closed : ClosedSupport.Closed board cells) (cellsUnique : cells.Nodup)
    (holesUnique : holes.Nodup) : Normalizer board where
  good := Good cells holes
  decidableGood := inferInstance
  normalize := normalize cells holes
  equivalent := normalize_equivalent cells holes cellsUnique holesUnique
  respects := normalize_respects cells holes
  preserved := by
    intro s d t good checked
    exact ⟨ClosedSupport.step_within board cells closed s d t good.1 checked,
      step_boulders_nodup board s d t good.2.1 checked,
      (step_holes_sublist board s d t checked).nodup good.2.2.1,
      fun _ present => good.2.2.2 ((step_holes_sublist board s d t checked).subset present)⟩

theorem pattern_value_respects {board holes potential}
    (cert : PatternCorrection.Certificate board holes potential)
    (a b : State) (related : Equivalent a b) :
    PatternCorrection.value cert a = PatternCorrection.value cert b := by
  have good : PatternCorrection.Good board holes cert.allowance a ↔
      PatternCorrection.Good board holes cert.allowance b := by
    unfold PatternCorrection.Good
    have subset : a.holes ⊆ holes ↔ b.holes ⊆ holes := by
      constructor
      · intro h c present; exact h (related.holes.mem_iff.mpr present)
      · intro h c present; exact h (related.holes.mem_iff.mp present)
    rw [related.boulders.nodup_iff, subset, related.player,
      related.boulders.length_eq, related.holes.length_eq]
  have projection : PatternCorrection.project a.boulders = PatternCorrection.project b.boulders :=
    funext fun _ => related.boulders.contains_eq
  simp only [PatternCorrection.value, PatternCorrection.correction, good, related.player,
    projection, LowerBounds.Potential.value,
    weightSum_permutation _ related.boulders, weightSum_permutation _ related.holes]

/-- Clipping a universal potential at zero preserves the push bound. -/
theorem clip_stepBound (base : State → Int) (valid : LowerBounds.StepBound board base) :
    LowerBounds.StepBound board (fun s => max 0 (base s)) := by
  intro s d t checked
  have bound := valid s d t checked
  simp only [Int.ofNat_eq_natCast] at bound ⊢
  simp only [Int.max_def]
  split <;> split <;> omega

end NetHack.Sokoban.ListNormalizer
