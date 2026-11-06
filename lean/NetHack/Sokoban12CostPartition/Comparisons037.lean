/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5180 (p : Pattern) (guard : d917 p = 1) : d642 p ≤ (2 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d642, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5179 p hg
    simpa only [d642, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d642, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5166 p hg
    simpa only [d642, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5181 (p : Pattern) (guard : d917 p = 1) : d643 p ≤ (2 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d643, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5120 p hg
    simpa only [d643, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d643, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5170 p hg
    simpa only [d643, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5182 (p : Pattern) (guard : d917 p = 1) : d644 p ≤ (2 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d644, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5181 p hg
    simpa only [d644, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d644, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d644, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5183 (p : Pattern) (guard : d917 p = 1) : d645 p ≤ (2 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d645, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5182 p hg
    simpa only [d645, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d645, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5140 p hg
    simpa only [d645, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5184 (p : Pattern) (guard : d917 p = 1) : d646 p ≤ (2 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d646, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5131 p hg
    simpa only [d646, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d646, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5175 p hg
    simpa only [d646, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5185 (p : Pattern) (guard : d917 p = 1) : d647 p ≤ (2 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d647, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5184 p hg
    simpa only [d647, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d647, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5176 p hg
    simpa only [d647, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5186 (p : Pattern) (guard : d917 p = 1) : d648 p ≤ (2 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d648, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5185 p hg
    simpa only [d648, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d648, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5148 p hg
    simpa only [d648, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5187 (p : Pattern) (guard : d917 p = 1) : d649 p ≤ (2 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d649, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5183 p hg
    simpa only [d649, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d649, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5186 p hg
    simpa only [d649, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5188 (p : Pattern) (guard : d917 p = 1) : d650 p ≤ (2 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d650, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5187 p hg
    simpa only [d650, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d650, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5166 p hg
    simpa only [d650, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5189 (p : Pattern) (guard : d917 p = 1) : d651 p ≤ (2 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d651, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5180 p hg
    simpa only [d651, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d651, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5188 p hg
    simpa only [d651, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5190 (p : Pattern) (guard : d917 p = 1) : d652 p ≤ (2 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d652, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5172 p hg
    simpa only [d652, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d652, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5140 p hg
    simpa only [d652, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5191 (p : Pattern) (guard : d917 p = 1) : d653 p ≤ (2 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d653, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5177 p hg
    simpa only [d653, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d653, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5148 p hg
    simpa only [d653, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5192 (p : Pattern) (guard : d917 p = 1) : d654 p ≤ (2 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d654, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5190 p hg
    simpa only [d654, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d654, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5191 p hg
    simpa only [d654, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5193 (p : Pattern) (guard : d917 p = 1) : d655 p ≤ (2 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d655, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5192 p hg
    simpa only [d655, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d655, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5166 p hg
    simpa only [d655, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5194 (p : Pattern) (guard : d917 p = 1) : d656 p ≤ (2 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d656, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5193 p hg
    simpa only [d656, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d656, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5166 p hg
    simpa only [d656, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5195 (p : Pattern) (guard : d917 p = 1) : d657 p ≤ (2 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d657, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5189 p hg
    simpa only [d657, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d657, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5194 p hg
    simpa only [d657, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5196 (p : Pattern) (guard : d917 p = 1) : d658 p ≤ (2 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d658, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5168 p hg
    simpa only [d658, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d658, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5195 p hg
    simpa only [d658, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5197 (p : Pattern) (guard : d0 p = 1) : d28 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5198 (p : Pattern) (guard : d1175 p = 1) : d29 p ≤ (0 : Int) + d24 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1175, d29, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4953 p hg
    simpa only [d1175, d29, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d29, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5197 p hg
    simpa only [d1175, d29, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5199 (p : Pattern) (guard : d1175 p = 1) : d30 p ≤ (0 : Int) + d24 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1175, d30, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4958 p hg
    simpa only [d1175, d30, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d30, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5197 p hg
    simpa only [d1175, d30, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5200 (p : Pattern) (guard : d1175 p = 1) : d31 p ≤ (0 : Int) + d24 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5198 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5199 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5201 (p : Pattern) (guard : d0 p = 1) : d587 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5202 (p : Pattern) (guard : d1175 p = 1) : d588 p ≤ (0 : Int) + d525 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1175, d588, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4962 p hg
    simpa only [d1175, d588, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d588, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5201 p hg
    simpa only [d1175, d588, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5203 (p : Pattern) (guard : d1175 p = 1) : d589 p ≤ (0 : Int) + d526 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d589, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5198 p hg
    simpa only [d589, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d589, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5202 p hg
    simpa only [d589, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5204 (p : Pattern) (guard : d1175 p = 1) : d590 p ≤ (0 : Int) + d525 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1175, d590, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4968 p hg
    simpa only [d1175, d590, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d590, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5201 p hg
    simpa only [d1175, d590, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5205 (p : Pattern) (guard : d1175 p = 1) : d591 p ≤ (0 : Int) + d526 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d591, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5199 p hg
    simpa only [d591, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d591, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5204 p hg
    simpa only [d591, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5206 (p : Pattern) (guard : d1175 p = 1) : d592 p ≤ (0 : Int) + d526 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5203 p hg
    simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5205 p hg
    simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5207 (p : Pattern) (guard : d1175 p = 1) : d593 p ≤ (0 : Int) + d527 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d593, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5200 p hg
    simpa only [d593, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d593, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5206 p hg
    simpa only [d593, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5208 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5209 (p : Pattern) (guard : d1175 p = 1) : d32 p ≤ (0 : Int) + d25 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1175, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4974 p hg
    simpa only [d1175, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5208 p hg
    simpa only [d1175, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5210 (p : Pattern) (guard : d1175 p = 1) : d33 p ≤ (0 : Int) + d26 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d33, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5199 p hg
    simpa only [d33, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d33, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5209 p hg
    simpa only [d33, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5211 (p : Pattern) (guard : d0 p = 1) : d594 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5212 (p : Pattern) (guard : d1175 p = 1) : d594 p ≤ (0 : Int) + d528 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1175, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4980 p hg
    simpa only [d1175, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5211 p hg
    simpa only [d1175, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5213 (p : Pattern) (guard : d1175 p = 1) : d595 p ≤ (0 : Int) + d529 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d595, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5209 p hg
    simpa only [d595, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d595, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5212 p hg
    simpa only [d595, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5214 (p : Pattern) (guard : d1175 p = 1) : d596 p ≤ (0 : Int) + d530 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d596, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5205 p hg
    simpa only [d596, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d596, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5213 p hg
    simpa only [d596, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5215 (p : Pattern) (guard : d1175 p = 1) : d597 p ≤ (0 : Int) + d531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d597, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5210 p hg
    simpa only [d597, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d597, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5214 p hg
    simpa only [d597, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5216 (p : Pattern) (guard : d1175 p = 1) : d598 p ≤ (0 : Int) + d532 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d598, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5207 p hg
    simpa only [d598, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d598, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5215 p hg
    simpa only [d598, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5217 (p : Pattern) (guard : d1175 p = 1) : d599 p ≤ (0 : Int) + d525 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5202 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5204 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5218 (p : Pattern) (guard : d1175 p = 1) : d600 p ≤ (0 : Int) + d533 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d600, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5200 p hg
    simpa only [d600, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d600, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d600, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5219 (p : Pattern) (guard : d1175 p = 1) : d601 p ≤ (0 : Int) + d534 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d601, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5198 p hg
    simpa only [d601, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d601, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5202 p hg
    simpa only [d601, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5220 (p : Pattern) (guard : d1175 p = 1) : d602 p ≤ (0 : Int) + d535 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d602, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5198 p hg
    simpa only [d602, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d602, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5219 p hg
    simpa only [d602, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5221 (p : Pattern) (guard : d1175 p = 1) : d603 p ≤ (0 : Int) + d534 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d603, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5199 p hg
    simpa only [d603, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d603, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5204 p hg
    simpa only [d603, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5222 (p : Pattern) (guard : d1175 p = 1) : d604 p ≤ (0 : Int) + d535 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d604, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5199 p hg
    simpa only [d604, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d604, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5221 p hg
    simpa only [d604, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5223 (p : Pattern) (guard : d1175 p = 1) : d605 p ≤ (0 : Int) + d535 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5220 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5222 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5224 (p : Pattern) (guard : d1175 p = 1) : d606 p ≤ (0 : Int) + d536 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d606, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5223 p hg
    simpa only [d606, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d606, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d606, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5225 (p : Pattern) (guard : d1175 p = 1) : d607 p ≤ (0 : Int) + d537 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d607, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5218 p hg
    simpa only [d607, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d607, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5224 p hg
    simpa only [d607, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5226 (p : Pattern) (guard : d1175 p = 1) : d608 p ≤ (0 : Int) + d538 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d608, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5218 p hg
    simpa only [d608, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d608, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5225 p hg
    simpa only [d608, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5227 (p : Pattern) (guard : d1175 p = 1) : d609 p ≤ (0 : Int) + d539 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d609, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5204 p hg
    simpa only [d609, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d609, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5212 p hg
    simpa only [d609, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5228 (p : Pattern) (guard : d1175 p = 1) : d610 p ≤ (0 : Int) + d540 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d610, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5210 p hg
    simpa only [d610, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d610, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5227 p hg
    simpa only [d610, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5229 (p : Pattern) (guard : d1175 p = 1) : d611 p ≤ (0 : Int) + d541 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d611, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5209 p hg
    simpa only [d611, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d611, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5212 p hg
    simpa only [d611, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5230 (p : Pattern) (guard : d1175 p = 1) : d612 p ≤ (0 : Int) + d542 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d612, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5209 p hg
    simpa only [d612, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d612, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5229 p hg
    simpa only [d612, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5231 (p : Pattern) (guard : d1175 p = 1) : d613 p ≤ (0 : Int) + d543 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d613, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5222 p hg
    simpa only [d613, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d613, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5230 p hg
    simpa only [d613, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5232 (p : Pattern) (guard : d1175 p = 1) : d614 p ≤ (0 : Int) + d544 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d614, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5231 p hg
    simpa only [d614, d544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d614, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5227 p hg
    simpa only [d614, d544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5233 (p : Pattern) (guard : d1175 p = 1) : d615 p ≤ (0 : Int) + d545 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d615, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5228 p hg
    simpa only [d615, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d615, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5232 p hg
    simpa only [d615, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5234 (p : Pattern) (guard : d1175 p = 1) : d616 p ≤ (0 : Int) + d546 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d616, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5228 p hg
    simpa only [d616, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d616, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5233 p hg
    simpa only [d616, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5235 (p : Pattern) (guard : d1175 p = 1) : d617 p ≤ (0 : Int) + d547 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d617, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5226 p hg
    simpa only [d617, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d617, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5234 p hg
    simpa only [d617, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5236 (p : Pattern) (guard : d1175 p = 1) : d618 p ≤ (0 : Int) + d548 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d618, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5216 p hg
    simpa only [d618, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d618, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5235 p hg
    simpa only [d618, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5237 (p : Pattern) (guard : d1175 p = 1) : d619 p ≤ (0 : Int) + d549 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d619, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5207 p hg
    simpa only [d619, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d619, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d619, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5238 (p : Pattern) (guard : d1175 p = 1) : d620 p ≤ (0 : Int) + d550 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d620, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5215 p hg
    simpa only [d620, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d620, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5227 p hg
    simpa only [d620, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5239 (p : Pattern) (guard : d1175 p = 1) : d621 p ≤ (0 : Int) + d551 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d621, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5237 p hg
    simpa only [d621, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d621, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5238 p hg
    simpa only [d621, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5240 (p : Pattern) (guard : d1175 p = 1) : d622 p ≤ (0 : Int) + d552 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d622, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5225 p hg
    simpa only [d622, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d622, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d622, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5241 (p : Pattern) (guard : d1175 p = 1) : d623 p ≤ (0 : Int) + d553 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d623, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5233 p hg
    simpa only [d623, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d623, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5227 p hg
    simpa only [d623, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5242 (p : Pattern) (guard : d1175 p = 1) : d624 p ≤ (0 : Int) + d554 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d624, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5240 p hg
    simpa only [d624, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d624, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5241 p hg
    simpa only [d624, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5243 (p : Pattern) (guard : d1175 p = 1) : d625 p ≤ (0 : Int) + d555 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d625, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5239 p hg
    simpa only [d625, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d625, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5242 p hg
    simpa only [d625, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5244 (p : Pattern) (guard : d1175 p = 1) : d626 p ≤ (0 : Int) + d556 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d626, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5236 p hg
    simpa only [d626, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d626, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5243 p hg
    simpa only [d626, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5245 (p : Pattern) (guard : d1175 p = 1) : d627 p ≤ (0 : Int) + d557 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d627, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d627, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d627, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5227 p hg
    simpa only [d627, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5246 (p : Pattern) (guard : d1175 p = 1) : d628 p ≤ (0 : Int) + d558 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d628, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5243 p hg
    simpa only [d628, d558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d628, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5245 p hg
    simpa only [d628, d558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5247 (p : Pattern) (guard : d1175 p = 1) : d629 p ≤ (0 : Int) + d559 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d629, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5244 p hg
    simpa only [d629, d559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d629, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5246 p hg
    simpa only [d629, d559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5248 (p : Pattern) (guard : d1175 p = 1) : d630 p ≤ (0 : Int) + d560 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d630, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5219 p hg
    simpa only [d630, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d630, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5202 p hg
    simpa only [d630, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5249 (p : Pattern) (guard : d1175 p = 1) : d631 p ≤ (0 : Int) + d560 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d631, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5221 p hg
    simpa only [d631, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d631, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5204 p hg
    simpa only [d631, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5250 (p : Pattern) (guard : d1175 p = 1) : d632 p ≤ (0 : Int) + d560 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5248 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5249 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5251 (p : Pattern) (guard : d1175 p = 1) : d633 p ≤ (0 : Int) + d561 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d633, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5223 p hg
    simpa only [d633, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d633, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d633, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5252 (p : Pattern) (guard : d1175 p = 1) : d634 p ≤ (0 : Int) + d562 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d634, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5207 p hg
    simpa only [d634, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d634, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5251 p hg
    simpa only [d634, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5253 (p : Pattern) (guard : d1175 p = 1) : d635 p ≤ (0 : Int) + d563 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d635, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5207 p hg
    simpa only [d635, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d635, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5252 p hg
    simpa only [d635, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5254 (p : Pattern) (guard : d1175 p = 1) : d636 p ≤ (0 : Int) + d564 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d636, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5229 p hg
    simpa only [d636, d564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d636, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5212 p hg
    simpa only [d636, d564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5255 (p : Pattern) (guard : d1175 p = 1) : d637 p ≤ (0 : Int) + d565 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d637, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5249 p hg
    simpa only [d637, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d637, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5254 p hg
    simpa only [d637, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5256 (p : Pattern) (guard : d1175 p = 1) : d638 p ≤ (0 : Int) + d566 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d638, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5231 p hg
    simpa only [d638, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d638, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5255 p hg
    simpa only [d638, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5257 (p : Pattern) (guard : d1175 p = 1) : d639 p ≤ (0 : Int) + d567 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d639, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5215 p hg
    simpa only [d639, d567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d639, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5256 p hg
    simpa only [d639, d567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5258 (p : Pattern) (guard : d1175 p = 1) : d640 p ≤ (0 : Int) + d568 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d640, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5215 p hg
    simpa only [d640, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d640, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5257 p hg
    simpa only [d640, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5259 (p : Pattern) (guard : d1175 p = 1) : d641 p ≤ (0 : Int) + d569 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d641, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5253 p hg
    simpa only [d641, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d641, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5258 p hg
    simpa only [d641, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5260 (p : Pattern) (guard : d1175 p = 1) : d642 p ≤ (0 : Int) + d570 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d642, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5259 p hg
    simpa only [d642, d570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d642, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5245 p hg
    simpa only [d642, d570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5261 (p : Pattern) (guard : d1175 p = 1) : d643 p ≤ (0 : Int) + d571 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d643, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5200 p hg
    simpa only [d643, d571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d643, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d643, d571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5262 (p : Pattern) (guard : d1175 p = 1) : d644 p ≤ (0 : Int) + d572 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d644, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5261 p hg
    simpa only [d644, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d644, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5251 p hg
    simpa only [d644, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5263 (p : Pattern) (guard : d1175 p = 1) : d645 p ≤ (0 : Int) + d573 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d645, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5262 p hg
    simpa only [d645, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d645, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d645, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5264 (p : Pattern) (guard : d1175 p = 1) : d646 p ≤ (0 : Int) + d574 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d646, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5210 p hg
    simpa only [d646, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d646, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5255 p hg
    simpa only [d646, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5265 (p : Pattern) (guard : d1175 p = 1) : d647 p ≤ (0 : Int) + d575 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d647, d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5264 p hg
    simpa only [d647, d575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d647, d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5256 p hg
    simpa only [d647, d575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5266 (p : Pattern) (guard : d1175 p = 1) : d648 p ≤ (0 : Int) + d576 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d648, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5265 p hg
    simpa only [d648, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d648, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5227 p hg
    simpa only [d648, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5267 (p : Pattern) (guard : d1175 p = 1) : d649 p ≤ (0 : Int) + d577 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d649, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5263 p hg
    simpa only [d649, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d649, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5266 p hg
    simpa only [d649, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5268 (p : Pattern) (guard : d1175 p = 1) : d650 p ≤ (0 : Int) + d578 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d650, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5267 p hg
    simpa only [d650, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d650, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5245 p hg
    simpa only [d650, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5269 (p : Pattern) (guard : d1175 p = 1) : d651 p ≤ (0 : Int) + d579 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d651, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5260 p hg
    simpa only [d651, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d651, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5268 p hg
    simpa only [d651, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5270 (p : Pattern) (guard : d1175 p = 1) : d652 p ≤ (0 : Int) + d580 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d652, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5252 p hg
    simpa only [d652, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d652, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d652, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5271 (p : Pattern) (guard : d1175 p = 1) : d653 p ≤ (0 : Int) + d581 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d653, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5257 p hg
    simpa only [d653, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d653, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5227 p hg
    simpa only [d653, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5272 (p : Pattern) (guard : d1175 p = 1) : d654 p ≤ (0 : Int) + d582 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d654, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5270 p hg
    simpa only [d654, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d654, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5271 p hg
    simpa only [d654, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5273 (p : Pattern) (guard : d1175 p = 1) : d655 p ≤ (0 : Int) + d583 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d655, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5272 p hg
    simpa only [d655, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d655, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5245 p hg
    simpa only [d655, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5274 (p : Pattern) (guard : d1175 p = 1) : d656 p ≤ (0 : Int) + d584 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d656, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5273 p hg
    simpa only [d656, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d656, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5245 p hg
    simpa only [d656, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5275 (p : Pattern) (guard : d1175 p = 1) : d657 p ≤ (0 : Int) + d585 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d657, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5269 p hg
    simpa only [d657, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d657, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5274 p hg
    simpa only [d657, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5276 (p : Pattern) (guard : d1175 p = 1) : d658 p ≤ (0 : Int) + d586 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d658, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5247 p hg
    simpa only [d658, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d658, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5275 p hg
    simpa only [d658, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5277 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5278 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5279 (p : Pattern) (guard : d917 p = 1) : d28 p ≤ (0 : Int) + d0 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d917, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5278 p hg
    simpa only [d917, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5280 (p : Pattern) (guard : d1174 p = 1) : d29 p ≤ (0 : Int) + d0 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5277 p hg
    simpa only [d1174, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1174, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5279 p hg
    simpa only [d1174, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5281 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5282 (p : Pattern) (guard : d1174 p = 1) : d30 p ≤ (0 : Int) + d0 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5281 p hg
    simpa only [d1174, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1174, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5279 p hg
    simpa only [d1174, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5283 (p : Pattern) (guard : d1174 p = 1) : d31 p ≤ (0 : Int) + d0 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5280 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5282 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5284 (p : Pattern) (guard : d0 p = 1) : d54 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5285 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5286 (p : Pattern) (guard : d917 p = 1) : d587 p ≤ (0 : Int) + d2 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d917, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5285 p hg
    simpa only [d917, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5287 (p : Pattern) (guard : d1174 p = 1) : d588 p ≤ (0 : Int) + d2 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5284 p hg
    simpa only [d1174, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1174, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5286 p hg
    simpa only [d1174, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5288 (p : Pattern) (guard : d1174 p = 1) : d589 p ≤ (0 : Int) + d45 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d589, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5280 p hg
    simpa only [d589, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d589, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5287 p hg
    simpa only [d589, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5289 (p : Pattern) (guard : d0 p = 1) : d259 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5290 (p : Pattern) (guard : d1174 p = 1) : d590 p ≤ (0 : Int) + d2 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5289 p hg
    simpa only [d1174, d590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1174, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5286 p hg
    simpa only [d1174, d590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5291 (p : Pattern) (guard : d1174 p = 1) : d591 p ≤ (0 : Int) + d45 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d591, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5282 p hg
    simpa only [d591, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d591, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5290 p hg
    simpa only [d591, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5292 (p : Pattern) (guard : d1174 p = 1) : d592 p ≤ (0 : Int) + d45 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5288 p hg
    simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5291 p hg
    simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5293 (p : Pattern) (guard : d1174 p = 1) : d593 p ≤ (0 : Int) + d46 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d593, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5283 p hg
    simpa only [d593, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d593, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5292 p hg
    simpa only [d593, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5294 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5295 (p : Pattern) (guard : d1174 p = 1) : d32 p ≤ (0 : Int) + d8 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5294 p hg
    simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4974 p hg
    simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5296 (p : Pattern) (guard : d1174 p = 1) : d33 p ≤ (0 : Int) + d1055 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d33, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5282 p hg
    simpa only [d33, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d33, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5295 p hg
    simpa only [d33, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5297 (p : Pattern) (guard : d0 p = 1) : d594 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5298 (p : Pattern) (guard : d1174 p = 1) : d594 p ≤ (0 : Int) + d9 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5297 p hg
    simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4980 p hg
    simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5299 (p : Pattern) (guard : d1174 p = 1) : d595 p ≤ (0 : Int) + d1056 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d595, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5295 p hg
    simpa only [d595, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d595, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5298 p hg
    simpa only [d595, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5300 (p : Pattern) (guard : d1174 p = 1) : d596 p ≤ (0 : Int) + d1057 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d596, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5291 p hg
    simpa only [d596, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d596, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5299 p hg
    simpa only [d596, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5301 (p : Pattern) (guard : d1174 p = 1) : d597 p ≤ (0 : Int) + d1058 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d597, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5296 p hg
    simpa only [d597, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d597, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5300 p hg
    simpa only [d597, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5302 (p : Pattern) (guard : d1174 p = 1) : d598 p ≤ (0 : Int) + d1059 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d598, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5293 p hg
    simpa only [d598, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d598, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5301 p hg
    simpa only [d598, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5303 (p : Pattern) (guard : d1174 p = 1) : d599 p ≤ (0 : Int) + d2 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5287 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5290 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5304 (p : Pattern) (guard : d1174 p = 1) : d600 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d600, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5283 p hg
    simpa only [d600, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d600, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5303 p hg
    simpa only [d600, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5305 (p : Pattern) (guard : d1174 p = 1) : d601 p ≤ (0 : Int) + d82 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d601, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5280 p hg
    simpa only [d601, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d601, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5287 p hg
    simpa only [d601, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5306 (p : Pattern) (guard : d1174 p = 1) : d602 p ≤ (0 : Int) + d83 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d602, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5280 p hg
    simpa only [d602, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d602, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5305 p hg
    simpa only [d602, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5307 (p : Pattern) (guard : d1174 p = 1) : d603 p ≤ (0 : Int) + d82 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d603, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5282 p hg
    simpa only [d603, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d603, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5290 p hg
    simpa only [d603, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5308 (p : Pattern) (guard : d1174 p = 1) : d604 p ≤ (0 : Int) + d83 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d604, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5282 p hg
    simpa only [d604, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d604, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5307 p hg
    simpa only [d604, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5309 (p : Pattern) (guard : d1174 p = 1) : d605 p ≤ (0 : Int) + d83 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5306 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5308 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5310 (p : Pattern) (guard : d1174 p = 1) : d606 p ≤ (0 : Int) + d84 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d606, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5309 p hg
    simpa only [d606, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d606, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5303 p hg
    simpa only [d606, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5311 (p : Pattern) (guard : d1174 p = 1) : d607 p ≤ (0 : Int) + d85 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d607, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5304 p hg
    simpa only [d607, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d607, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5310 p hg
    simpa only [d607, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5312 (p : Pattern) (guard : d1174 p = 1) : d608 p ≤ (0 : Int) + d162 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d608, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5304 p hg
    simpa only [d608, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d608, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5311 p hg
    simpa only [d608, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5313 (p : Pattern) (guard : d1174 p = 1) : d609 p ≤ (0 : Int) + d1060 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d609, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5290 p hg
    simpa only [d609, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d609, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5298 p hg
    simpa only [d609, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5314 (p : Pattern) (guard : d1174 p = 1) : d610 p ≤ (0 : Int) + d1061 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d610, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5296 p hg
    simpa only [d610, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d610, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5313 p hg
    simpa only [d610, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5315 (p : Pattern) (guard : d1174 p = 1) : d611 p ≤ (0 : Int) + d1062 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d611, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5295 p hg
    simpa only [d611, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d611, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5298 p hg
    simpa only [d611, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5316 (p : Pattern) (guard : d1174 p = 1) : d612 p ≤ (0 : Int) + d1063 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d612, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5295 p hg
    simpa only [d612, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d612, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5315 p hg
    simpa only [d612, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5317 (p : Pattern) (guard : d1174 p = 1) : d613 p ≤ (0 : Int) + d1064 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d613, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5308 p hg
    simpa only [d613, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d613, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5316 p hg
    simpa only [d613, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5318 (p : Pattern) (guard : d1174 p = 1) : d614 p ≤ (0 : Int) + d1065 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d614, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5317 p hg
    simpa only [d614, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d614, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5313 p hg
    simpa only [d614, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5319 (p : Pattern) (guard : d1174 p = 1) : d615 p ≤ (0 : Int) + d1066 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d615, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5314 p hg
    simpa only [d615, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d615, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5318 p hg
    simpa only [d615, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
