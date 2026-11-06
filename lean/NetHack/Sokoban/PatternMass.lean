/- Exact occupancy counts and the availability guard for forgotten boulders.
These facts are about arbitrary Boolean patterns and the actual ordered Model
lists. In particular an untracked source requires a strictly positive supply
of untracked boulders; projection never creates an infinite supply. -/
import NetHack.Sokoban.DecisionDAGCounted
import NetHack.Sokoban.ClosedSupport
import NetHack.Sokoban.HazardPattern

namespace NetHack.Sokoban.PatternMass
open PatternCorrection

def mass (cells : List Cell) (p : Pattern) : Nat := (cells.filter p).length

theorem count_eq_mass (cells : List Cell) (p : Pattern) :
    DecisionDAGCounted.count cells p = Int.ofNat (mass cells p) := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    cases selected : p cell <;> simp [DecisionDAGCounted.count, mass, selected] at ih ⊢ <;> omega

theorem mass_mono (small large : List Cell) (p : Pattern) (unique : small.Nodup)
    (subset : small ⊆ large) : mass small p ≤ mass large p := by
  apply List.Nodup.length_le_of_subset (unique.filter p)
  intro cell member
  rcases List.mem_filter.mp member with ⟨present, selected⟩
  exact List.mem_filter.mpr ⟨subset present, selected⟩

theorem mass_extra (small large : List Cell) (p : Pattern) (unique : small.Nodup)
    (subset : small ⊆ large) (source : Cell) (present : source ∈ large)
    (selected : p source = true) (untracked : source ∉ small) :
    mass small p < mass large p := by
  have extra : source ∈ large.filter p := List.mem_filter.mpr ⟨present, selected⟩
  have strictSubset : small.filter p ⊆ (large.filter p).erase source := by
    intro cell member
    rcases List.mem_filter.mp member with ⟨inside, occupied⟩
    have different : cell ≠ source := by intro same; subst cell; exact untracked inside
    exact (List.mem_erase_of_ne different).mpr (List.mem_filter.mpr ⟨subset inside, occupied⟩)
  have shorter := List.Nodup.length_le_of_subset (unique.filter p) strictSubset
  have erased := List.length_erase_of_mem extra
  have positive := List.length_pos_of_mem extra
  unfold mass
  omega

theorem project_mass (cells boxes : List Cell) (cellsUnique : cells.Nodup)
    (boxesUnique : boxes.Nodup) (subset : boxes ⊆ cells) :
    mass cells (project boxes) = boxes.length :=
  ClosedSupport.projection_length cells boxes cellsUnique boxesUnique subset

theorem project_filter_at (cells : List Cell) (p : Pattern) (cell : Cell)
    (member : cell ∈ cells) : project (cells.filter p) cell = p cell := by
  apply Bool.eq_iff_iff.mpr
  simp [project, List.mem_filter, member]

theorem mask_project_filter (cells : List Cell) (p : Pattern) :
    HazardPattern.boxes cells p = project (cells.filter p) := by
  funext cell
  apply Bool.eq_iff_iff.mpr
  simp [HazardPattern.boxes, project, List.mem_filter]

theorem count_erase (cells : List Cell) (p : Pattern) (source : Cell)
    (present : p source = true) :
    DecisionDAGCounted.count cells (change p source none) =
      DecisionDAGCounted.count cells p -
        Int.ofNat ((cells.filter (fun cell => decide (cell = source))).length) := by
  have masked : DecisionDAGCounted.count cells (change p source none) =
      DecisionDAGCounted.count (cells.filter (fun cell => decide (cell ≠ source))) p := by
    induction cells with
    | nil => rfl
    | cons cell cells ih =>
      by_cases same : cell = source
      · subst cell
        simp [DecisionDAGCounted.count, change, ih]
      · have opposite : source ≠ cell := Ne.symm same
        simp [DecisionDAGCounted.count, change, same, opposite, ih]
  rw [masked, DecisionDAGCounted.count_split cells p source true present]
  rfl

end NetHack.Sokoban.PatternMass
