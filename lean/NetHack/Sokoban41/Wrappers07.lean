/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers06
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_walk245_0 (pattern : Ten) : walkGuard ⟨121,134,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk245_0 : WalkBound ⟨121,134,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk245_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk245_1 (pattern : Ten) : walkGuard ⟨121,134,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk245_1 : WalkBound ⟨121,134,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk245_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk246_0 (pattern : Ten) : walkGuard ⟨121,106,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk246_0 : WalkBound ⟨121,106,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk246_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk246_1 (pattern : Ten) : walkGuard ⟨121,106,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk246_1 : WalkBound ⟨121,106,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk246_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk247_0 (pattern : Ten) : walkGuard ⟨122,108,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk247_0 : WalkBound ⟨122,108,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk247_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk247_1 (pattern : Ten) : walkGuard ⟨122,108,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk247_1 : WalkBound ⟨122,108,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk247_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk248_0 (pattern : Ten) : walkGuard ⟨122,123,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk248_0 : WalkBound ⟨122,123,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk248_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk248_1 (pattern : Ten) : walkGuard ⟨122,123,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk248_1 : WalkBound ⟨122,123,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk248_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk249_0 (pattern : Ten) : walkGuard ⟨122,136,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk249_0 : WalkBound ⟨122,136,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk249_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk249_1 (pattern : Ten) : walkGuard ⟨122,136,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk249_1 : WalkBound ⟨122,136,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk249_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk250_0 (pattern : Ten) : walkGuard ⟨122,121,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk250_0 : WalkBound ⟨122,121,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk250_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk250_1 (pattern : Ten) : walkGuard ⟨122,121,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk250_1 : WalkBound ⟨122,121,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk250_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk251_0 (pattern : Ten) : walkGuard ⟨122,109,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk251_0 : WalkBound ⟨122,109,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk251_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk251_1 (pattern : Ten) : walkGuard ⟨122,109,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk251_1 : WalkBound ⟨122,109,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk251_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk252_0 (pattern : Ten) : walkGuard ⟨122,137,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk252_0 : WalkBound ⟨122,137,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk252_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk252_1 (pattern : Ten) : walkGuard ⟨122,137,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk252_1 : WalkBound ⟨122,137,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk252_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk253_0 (pattern : Ten) : walkGuard ⟨122,135,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk253_0 : WalkBound ⟨122,135,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk253_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk253_1 (pattern : Ten) : walkGuard ⟨122,135,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk253_1 : WalkBound ⟨122,135,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk253_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk254_0 (pattern : Ten) : walkGuard ⟨122,107,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk254_0 : WalkBound ⟨122,107,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk254_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk254_1 (pattern : Ten) : walkGuard ⟨122,107,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk254_1 : WalkBound ⟨122,107,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk254_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk255_0 (pattern : Ten) : walkGuard ⟨123,109,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk255_0 : WalkBound ⟨123,109,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk255_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk255_1 (pattern : Ten) : walkGuard ⟨123,109,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk255_1 : WalkBound ⟨123,109,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk255_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk256_0 (pattern : Ten) : walkGuard ⟨123,124,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk256_0 : WalkBound ⟨123,124,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk256_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk256_1 (pattern : Ten) : walkGuard ⟨123,124,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk256_1 : WalkBound ⟨123,124,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk256_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk257_0 (pattern : Ten) : walkGuard ⟨123,137,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk257_0 : WalkBound ⟨123,137,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk257_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk257_1 (pattern : Ten) : walkGuard ⟨123,137,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk257_1 : WalkBound ⟨123,137,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk257_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk258_0 (pattern : Ten) : walkGuard ⟨123,122,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk258_0 : WalkBound ⟨123,122,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk258_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk258_1 (pattern : Ten) : walkGuard ⟨123,122,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk258_1 : WalkBound ⟨123,122,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk258_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk259_0 (pattern : Ten) : walkGuard ⟨123,110,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk259_0 : WalkBound ⟨123,110,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk259_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk259_1 (pattern : Ten) : walkGuard ⟨123,110,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk259_1 : WalkBound ⟨123,110,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk259_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk260_0 (pattern : Ten) : walkGuard ⟨123,138,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk260_0 : WalkBound ⟨123,138,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk260_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk260_1 (pattern : Ten) : walkGuard ⟨123,138,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk260_1 : WalkBound ⟨123,138,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk260_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk261_0 (pattern : Ten) : walkGuard ⟨123,136,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk261_0 : WalkBound ⟨123,136,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk261_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk261_1 (pattern : Ten) : walkGuard ⟨123,136,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk261_1 : WalkBound ⟨123,136,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk261_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk262_0 (pattern : Ten) : walkGuard ⟨123,108,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk262_0 : WalkBound ⟨123,108,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk262_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk262_1 (pattern : Ten) : walkGuard ⟨123,108,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk262_1 : WalkBound ⟨123,108,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk262_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk263_0 (pattern : Ten) : walkGuard ⟨124,110,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk263_0 : WalkBound ⟨124,110,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk263_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk263_1 (pattern : Ten) : walkGuard ⟨124,110,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk263_1 : WalkBound ⟨124,110,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk263_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk264_0 (pattern : Ten) : walkGuard ⟨124,138,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk264_0 : WalkBound ⟨124,138,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk264_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk264_1 (pattern : Ten) : walkGuard ⟨124,138,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk264_1 : WalkBound ⟨124,138,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk264_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk265_0 (pattern : Ten) : walkGuard ⟨124,123,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk265_0 : WalkBound ⟨124,123,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk265_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk265_1 (pattern : Ten) : walkGuard ⟨124,123,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk265_1 : WalkBound ⟨124,123,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk265_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk266_0 (pattern : Ten) : walkGuard ⟨124,137,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk266_0 : WalkBound ⟨124,137,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk266_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk266_1 (pattern : Ten) : walkGuard ⟨124,137,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk266_1 : WalkBound ⟨124,137,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk266_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk267_0 (pattern : Ten) : walkGuard ⟨124,109,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk267_0 : WalkBound ⟨124,109,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk267_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk267_1 (pattern : Ten) : walkGuard ⟨124,109,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk267_1 : WalkBound ⟨124,109,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk267_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk268_0 (pattern : Ten) : walkGuard ⟨128,114,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk268_0 : WalkBound ⟨128,114,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk268_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk268_1 (pattern : Ten) : walkGuard ⟨128,114,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk268_1 : WalkBound ⟨128,114,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk268_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk269_0 (pattern : Ten) : walkGuard ⟨128,142,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk269_0 : WalkBound ⟨128,142,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk269_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk269_1 (pattern : Ten) : walkGuard ⟨128,142,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk269_1 : WalkBound ⟨128,142,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk269_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk270_0 (pattern : Ten) : walkGuard ⟨128,143,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk270_0 : WalkBound ⟨128,143,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk270_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk270_1 (pattern : Ten) : walkGuard ⟨128,143,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk270_1 : WalkBound ⟨128,143,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk270_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk271_0 (pattern : Ten) : walkGuard ⟨134,120,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk271_0 : WalkBound ⟨134,120,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk271_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk271_1 (pattern : Ten) : walkGuard ⟨134,120,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk271_1 : WalkBound ⟨134,120,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk271_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk272_0 (pattern : Ten) : walkGuard ⟨134,135,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk272_0 : WalkBound ⟨134,135,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk272_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk272_1 (pattern : Ten) : walkGuard ⟨134,135,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk272_1 : WalkBound ⟨134,135,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk272_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk273_0 (pattern : Ten) : walkGuard ⟨134,148,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk273_0 : WalkBound ⟨134,148,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk273_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk273_1 (pattern : Ten) : walkGuard ⟨134,148,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk273_1 : WalkBound ⟨134,148,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk273_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk274_0 (pattern : Ten) : walkGuard ⟨134,121,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk274_0 : WalkBound ⟨134,121,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk274_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk274_1 (pattern : Ten) : walkGuard ⟨134,121,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk274_1 : WalkBound ⟨134,121,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk274_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk275_0 (pattern : Ten) : walkGuard ⟨134,149,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk275_0 : WalkBound ⟨134,149,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk275_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk275_1 (pattern : Ten) : walkGuard ⟨134,149,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk275_1 : WalkBound ⟨134,149,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk275_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk276_0 (pattern : Ten) : walkGuard ⟨134,147,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk276_0 : WalkBound ⟨134,147,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk276_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk276_1 (pattern : Ten) : walkGuard ⟨134,147,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk276_1 : WalkBound ⟨134,147,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk276_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk277_0 (pattern : Ten) : walkGuard ⟨135,121,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk277_0 : WalkBound ⟨135,121,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk277_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk277_1 (pattern : Ten) : walkGuard ⟨135,121,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk277_1 : WalkBound ⟨135,121,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk277_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk278_0 (pattern : Ten) : walkGuard ⟨135,136,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk278_0 : WalkBound ⟨135,136,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk278_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk278_1 (pattern : Ten) : walkGuard ⟨135,136,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk278_1 : WalkBound ⟨135,136,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk278_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk279_0 (pattern : Ten) : walkGuard ⟨135,149,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk279_0 : WalkBound ⟨135,149,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk279_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk279_1 (pattern : Ten) : walkGuard ⟨135,149,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk279_1 : WalkBound ⟨135,149,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk279_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban41
