/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons236
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare33180 (p : Pattern) (guard : d6558 p = 1) : d3173 p ≤ (2 : Int) + d7603 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3173, d7603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33176 p hg
    simpa only [d3173, d7603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3173, d7603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33179 p hg
    simpa only [d3173, d7603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33181 (p : Pattern) (guard : d6558 p = 1) : d3174 p ≤ (2 : Int) + d7604 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3174, d7604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33173 p hg
    simpa only [d3174, d7604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3174, d7604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33180 p hg
    simpa only [d3174, d7604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33182 (p : Pattern) (guard : d6558 p = 1) : d3175 p ≤ (2 : Int) + d7605 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3175, d7605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32944 p hg
    simpa only [d3175, d7605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3175, d7605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32940 p hg
    simpa only [d3175, d7605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33183 (p : Pattern) (guard : d6558 p = 1) : d3176 p ≤ (2 : Int) + d7606 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3176, d7606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32941 p hg
    simpa only [d3176, d7606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3176, d7606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33182 p hg
    simpa only [d3176, d7606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33184 (p : Pattern) (guard : d6558 p = 1) : d3177 p ≤ (2 : Int) + d7607 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3177, d7607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32937 p hg
    simpa only [d3177, d7607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3177, d7607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33183 p hg
    simpa only [d3177, d7607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33185 (p : Pattern) (guard : d6558 p = 1) : d2126 p ≤ (2 : Int) + d7608 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2126, d7608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32985 p hg
    simpa only [d2126, d7608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2126, d7608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2126, d7608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33186 (p : Pattern) (guard : d6558 p = 1) : d3178 p ≤ (2 : Int) + d7609 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3178, d7609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33184 p hg
    simpa only [d3178, d7609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3178, d7609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33185 p hg
    simpa only [d3178, d7609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33187 (p : Pattern) (guard : d6558 p = 1) : d3179 p ≤ (2 : Int) + d7610 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3179, d7610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33168 p hg
    simpa only [d3179, d7610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3179, d7610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33186 p hg
    simpa only [d3179, d7610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33188 (p : Pattern) (guard : d6558 p = 1) : d2135 p ≤ (2 : Int) + d7264 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2135, d7264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32909 p hg
    simpa only [d2135, d7264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2135, d7264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32969 p hg
    simpa only [d2135, d7264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33189 (p : Pattern) (guard : d6558 p = 1) : d2136 p ≤ (2 : Int) + d7611 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2136, d7611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32970 p hg
    simpa only [d2136, d7611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2136, d7611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33188 p hg
    simpa only [d2136, d7611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33190 (p : Pattern) (guard : d6558 p = 1) : d3180 p ≤ (2 : Int) + d7612 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3180, d7612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32906 p hg
    simpa only [d3180, d7612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3180, d7612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33189 p hg
    simpa only [d3180, d7612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33191 (p : Pattern) (guard : d6558 p = 1) : d2131 p ≤ (2 : Int) + d7613 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2131, d7613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32911 p hg
    simpa only [d2131, d7613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2131, d7613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2131, d7613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33192 (p : Pattern) (guard : d6558 p = 1) : d3181 p ≤ (2 : Int) + d7614 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3181, d7614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33190 p hg
    simpa only [d3181, d7614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3181, d7614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33191 p hg
    simpa only [d3181, d7614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33193 (p : Pattern) (guard : d6558 p = 1) : d3182 p ≤ (2 : Int) + d7615 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3182, d7615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33192 p hg
    simpa only [d3182, d7615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3182, d7615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3182, d7615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33194 (p : Pattern) (guard : d6558 p = 1) : d3183 p ≤ (2 : Int) + d7616 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3183, d7616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33187 p hg
    simpa only [d3183, d7616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3183, d7616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33193 p hg
    simpa only [d3183, d7616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33195 (p : Pattern) (guard : d6558 p = 1) : d2137 p ≤ (2 : Int) + d7617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2137, d7617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33189 p hg
    simpa only [d2137, d7617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2137, d7617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2137, d7617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33196 (p : Pattern) (guard : d6558 p = 1) : d3184 p ≤ (2 : Int) + d7618 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3184, d7618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32976 p hg
    simpa only [d3184, d7618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3184, d7618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33195 p hg
    simpa only [d3184, d7618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33197 (p : Pattern) (guard : d6558 p = 1) : d3185 p ≤ (2 : Int) + d7619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3185, d7619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33196 p hg
    simpa only [d3185, d7619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3185, d7619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3185, d7619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33198 (p : Pattern) (guard : d6558 p = 1) : d3186 p ≤ (2 : Int) + d7620 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3186, d7620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33197 p hg
    simpa only [d3186, d7620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3186, d7620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3186, d7620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33199 (p : Pattern) (guard : d6558 p = 1) : d3187 p ≤ (2 : Int) + d7621 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3187, d7621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33194 p hg
    simpa only [d3187, d7621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3187, d7621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33198 p hg
    simpa only [d3187, d7621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33200 (p : Pattern) (guard : d6558 p = 1) : d3188 p ≤ (2 : Int) + d7622 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3188, d7622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32976 p hg
    simpa only [d3188, d7622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3188, d7622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32963 p hg
    simpa only [d3188, d7622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33201 (p : Pattern) (guard : d6558 p = 1) : d3189 p ≤ (2 : Int) + d7623 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3189, d7623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33200 p hg
    simpa only [d3189, d7623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3189, d7623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32977 p hg
    simpa only [d3189, d7623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33202 (p : Pattern) (guard : d6558 p = 1) : d3190 p ≤ (2 : Int) + d7624 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3190, d7624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33201 p hg
    simpa only [d3190, d7624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3190, d7624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33178 p hg
    simpa only [d3190, d7624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33203 (p : Pattern) (guard : d6558 p = 1) : d3191 p ≤ (2 : Int) + d7625 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3191, d7625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32780 p hg
    simpa only [d3191, d7625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3191, d7625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3191, d7625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33204 (p : Pattern) (guard : d6558 p = 1) : d3192 p ≤ (2 : Int) + d7626 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3192, d7626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33202 p hg
    simpa only [d3192, d7626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3192, d7626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33203 p hg
    simpa only [d3192, d7626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33205 (p : Pattern) (guard : d6558 p = 1) : d3193 p ≤ (2 : Int) + d7627 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3193, d7627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33199 p hg
    simpa only [d3193, d7627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3193, d7627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33204 p hg
    simpa only [d3193, d7627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33206 (p : Pattern) (guard : d6558 p = 1) : d3194 p ≤ (2 : Int) + d7628 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3194, d7628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33181 p hg
    simpa only [d3194, d7628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3194, d7628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33205 p hg
    simpa only [d3194, d7628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33207 (p : Pattern) (guard : d6558 p = 1) : d3195 p ≤ (2 : Int) + d7629 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3195, d7629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33026 p hg
    simpa only [d3195, d7629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3195, d7629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33029 p hg
    simpa only [d3195, d7629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33208 (p : Pattern) (guard : d6558 p = 1) : d3196 p ≤ (2 : Int) + d7630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3196, d7630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33036 p hg
    simpa only [d3196, d7630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3196, d7630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32809 p hg
    simpa only [d3196, d7630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33209 (p : Pattern) (guard : d6558 p = 1) : d3197 p ≤ (2 : Int) + d7631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3197, d7631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33207 p hg
    simpa only [d3197, d7631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3197, d7631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33208 p hg
    simpa only [d3197, d7631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33210 (p : Pattern) (guard : d6558 p = 1) : d3198 p ≤ (2 : Int) + d7632 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3198, d7632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33209 p hg
    simpa only [d3198, d7632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3198, d7632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33047 p hg
    simpa only [d3198, d7632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33211 (p : Pattern) (guard : d6558 p = 1) : d3199 p ≤ (2 : Int) + d7633 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3199, d7633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33210 p hg
    simpa only [d3199, d7633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3199, d7633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33051 p hg
    simpa only [d3199, d7633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33212 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33213 (p : Pattern) (guard : d5842 p = 1) : d2154 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33212 p hg
    simpa only [d5842, d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15733 p hg
    simpa only [d5842, d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33214 (p : Pattern) (guard : d6558 p = 1) : d2155 p ≤ (2 : Int) + d11 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33213 p hg
    simpa only [d6558, d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32705 p hg
    simpa only [d6558, d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33215 (p : Pattern) (guard : d6558 p = 1) : d2156 p ≤ (2 : Int) + d7634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2156, d7634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32944 p hg
    simpa only [d2156, d7634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2156, d7634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33214 p hg
    simpa only [d2156, d7634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33216 (p : Pattern) (guard : d6558 p = 1) : d2157 p ≤ (2 : Int) + d7635 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2157, d7635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32941 p hg
    simpa only [d2157, d7635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2157, d7635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33215 p hg
    simpa only [d2157, d7635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33217 (p : Pattern) (guard : d6558 p = 1) : d2158 p ≤ (2 : Int) + d7636 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2158, d7636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33216 p hg
    simpa only [d2158, d7636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2158, d7636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2158, d7636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33218 (p : Pattern) (guard : d6558 p = 1) : d3200 p ≤ (2 : Int) + d7637 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3200, d7637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33000 p hg
    simpa only [d3200, d7637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3200, d7637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33217 p hg
    simpa only [d3200, d7637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33219 (p : Pattern) (guard : d6558 p = 1) : d3201 p ≤ (2 : Int) + d7638 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3201, d7638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33218 p hg
    simpa only [d3201, d7638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3201, d7638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33036 p hg
    simpa only [d3201, d7638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33220 (p : Pattern) (guard : d6558 p = 1) : d3202 p ≤ (2 : Int) + d7639 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3202, d7639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33219 p hg
    simpa only [d3202, d7639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3202, d7639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33157 p hg
    simpa only [d3202, d7639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33221 (p : Pattern) (guard : d6558 p = 1) : d3203 p ≤ (2 : Int) + d7640 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3203, d7640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33220 p hg
    simpa only [d3203, d7640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3203, d7640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33050 p hg
    simpa only [d3203, d7640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33222 (p : Pattern) (guard : d6558 p = 1) : d3204 p ≤ (2 : Int) + d7641 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3204, d7641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32852 p hg
    simpa only [d3204, d7641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3204, d7641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3204, d7641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33223 (p : Pattern) (guard : d6558 p = 1) : d3205 p ≤ (2 : Int) + d7642 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3205, d7642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33222 p hg
    simpa only [d3205, d7642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3205, d7642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3205, d7642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33224 (p : Pattern) (guard : d6558 p = 1) : d3206 p ≤ (2 : Int) + d7643 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3206, d7643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33221 p hg
    simpa only [d3206, d7643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3206, d7643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33223 p hg
    simpa only [d3206, d7643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33225 (p : Pattern) (guard : d6558 p = 1) : d3207 p ≤ (2 : Int) + d7644 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3207, d7644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33211 p hg
    simpa only [d3207, d7644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3207, d7644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33224 p hg
    simpa only [d3207, d7644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33226 (p : Pattern) (guard : d6558 p = 1) : d3208 p ≤ (2 : Int) + d7645 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3208, d7645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33206 p hg
    simpa only [d3208, d7645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3208, d7645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33225 p hg
    simpa only [d3208, d7645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33227 (p : Pattern) (guard : d6558 p = 1) : d3209 p ≤ (2 : Int) + d7646 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3209, d7646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33036 p hg
    simpa only [d3209, d7646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3209, d7646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32851 p hg
    simpa only [d3209, d7646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33228 (p : Pattern) (guard : d6558 p = 1) : d3210 p ≤ (2 : Int) + d7647 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3210, d7647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33207 p hg
    simpa only [d3210, d7647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3210, d7647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33227 p hg
    simpa only [d3210, d7647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33229 (p : Pattern) (guard : d6558 p = 1) : d3211 p ≤ (2 : Int) + d7648 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3211, d7648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33031 p hg
    simpa only [d3211, d7648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3211, d7648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32851 p hg
    simpa only [d3211, d7648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33230 (p : Pattern) (guard : d6558 p = 1) : d3212 p ≤ (2 : Int) + d7649 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3212, d7649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33229 p hg
    simpa only [d3212, d7649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3212, d7649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3212, d7649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33231 (p : Pattern) (guard : d6558 p = 1) : d3213 p ≤ (2 : Int) + d7650 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3213, d7650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33228 p hg
    simpa only [d3213, d7650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3213, d7650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33230 p hg
    simpa only [d3213, d7650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33232 (p : Pattern) (guard : d6558 p = 1) : d3214 p ≤ (2 : Int) + d7651 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3214, d7651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33038 p hg
    simpa only [d3214, d7651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3214, d7651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32809 p hg
    simpa only [d3214, d7651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33233 (p : Pattern) (guard : d6558 p = 1) : d3215 p ≤ (2 : Int) + d7652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3215, d7652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33232 p hg
    simpa only [d3215, d7652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3215, d7652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3215, d7652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33234 (p : Pattern) (guard : d6558 p = 1) : d3216 p ≤ (2 : Int) + d7653 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3216, d7653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33233 p hg
    simpa only [d3216, d7653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3216, d7653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3216, d7653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33235 (p : Pattern) (guard : d6558 p = 1) : d3217 p ≤ (2 : Int) + d7654 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3217, d7654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33231 p hg
    simpa only [d3217, d7654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3217, d7654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33234 p hg
    simpa only [d3217, d7654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33236 (p : Pattern) (guard : d6558 p = 1) : d3218 p ≤ (2 : Int) + d7655 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3218, d7655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33235 p hg
    simpa only [d3218, d7655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3218, d7655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33224 p hg
    simpa only [d3218, d7655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33237 (p : Pattern) (guard : d6558 p = 1) : d3219 p ≤ (2 : Int) + d7656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3219, d7656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33236 p hg
    simpa only [d3219, d7656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3219, d7656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3219, d7656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33238 (p : Pattern) (guard : d6558 p = 1) : d3220 p ≤ (2 : Int) + d7657 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3220, d7657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33226 p hg
    simpa only [d3220, d7657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3220, d7657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33237 p hg
    simpa only [d3220, d7657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33239 (p : Pattern) (guard : d6558 p = 1) : d3221 p ≤ (2 : Int) + d7658 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3221, d7658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33165 p hg
    simpa only [d3221, d7658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3221, d7658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33238 p hg
    simpa only [d3221, d7658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33240 (p : Pattern) (guard : d6558 p = 1) : d3222 p ≤ (2 : Int) + d7659 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3222, d7659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32886 p hg
    simpa only [d3222, d7659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3222, d7659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33239 p hg
    simpa only [d3222, d7659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33241 (p : Pattern) (guard : d6558 p = 1) : d3223 p ≤ (2 : Int) + d7660 p := by
  cases selected : p 49 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3223, d7660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33146 p hg
    simpa only [d3223, d7660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3223, d7660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33240 p hg
    simpa only [d3223, d7660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33242 (p : Pattern) (guard : d6558 p = 1) : d3224 p ≤ (2 : Int) + d7661 p := by
  cases selected : p 48 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3224, d7661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33065 p hg
    simpa only [d3224, d7661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3224, d7661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33241 p hg
    simpa only [d3224, d7661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33243 (p : Pattern) (guard : d1 p = 1) : d3224 p ≤ (1 : Int) + d3224 p := by
  omega
theorem compare33244 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (2 : Int) + d0 p := by
  omega
theorem compare33245 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15806 p hg
    simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33246 (p : Pattern) (guard : d5843 p = 1) : d14 p ≤ (2 : Int) + d3226 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d14, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33244 p hg
    simpa only [d14, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d14, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33245 p hg
    simpa only [d14, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33247 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (2 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33248 (p : Pattern) (guard : d5843 p = 1) : d1769 p ≤ (2 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4694 p hg
    simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33247 p hg
    simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33249 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33250 (p : Pattern) (guard : d5843 p = 1) : d1770 p ≤ (2 : Int) + d3239 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1770, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33248 p hg
    simpa only [d1770, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1770, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33249 p hg
    simpa only [d1770, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33251 (p : Pattern) (guard : d5843 p = 1) : d1771 p ≤ (2 : Int) + d7662 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1771, d7662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33246 p hg
    simpa only [d1771, d7662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1771, d7662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33250 p hg
    simpa only [d1771, d7662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33252 (p : Pattern) (guard : d5843 p = 1) : d1772 p ≤ (2 : Int) + d7663 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1772, d7663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33251 p hg
    simpa only [d1772, d7663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1772, d7663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33250 p hg
    simpa only [d1772, d7663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33253 (p : Pattern) (guard : d5843 p = 1) : d2895 p ≤ (2 : Int) + d7664 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2895, d7664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33246 p hg
    simpa only [d2895, d7664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2895, d7664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33252 p hg
    simpa only [d2895, d7664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33254 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33255 (p : Pattern) (guard : d5843 p = 1) : d1683 p ≤ (2 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14025 p hg
    simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33254 p hg
    simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33256 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12151 p hg
    simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33257 (p : Pattern) (guard : d5843 p = 1) : d1684 p ≤ (2 : Int) + d3250 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1684, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33255 p hg
    simpa only [d1684, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1684, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33256 p hg
    simpa only [d1684, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33258 (p : Pattern) (guard : d5843 p = 1) : d1685 p ≤ (2 : Int) + d7665 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1685, d7665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33246 p hg
    simpa only [d1685, d7665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1685, d7665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33257 p hg
    simpa only [d1685, d7665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33259 (p : Pattern) (guard : d5843 p = 1) : d1686 p ≤ (2 : Int) + d7666 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1686, d7666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33258 p hg
    simpa only [d1686, d7666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1686, d7666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33257 p hg
    simpa only [d1686, d7666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33260 (p : Pattern) (guard : d5843 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare33261 (p : Pattern) (guard : d5843 p = 1) : d1687 p ≤ (2 : Int) + d7667 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1687, d7667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33259 p hg
    simpa only [d1687, d7667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1687, d7667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1687, d7667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33262 (p : Pattern) (guard : d5843 p = 1) : d2896 p ≤ (2 : Int) + d7668 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2896, d7668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33253 p hg
    simpa only [d2896, d7668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2896, d7668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33261 p hg
    simpa only [d2896, d7668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33263 (p : Pattern) (guard : d5843 p = 1) : d4 p ≤ (2 : Int) + d4 p := by
  omega
theorem compare33264 (p : Pattern) (guard : d5843 p = 1) : d18 p ≤ (2 : Int) + d3239 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d18, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33263 p hg
    simpa only [d18, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d18, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33249 p hg
    simpa only [d18, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33265 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (2 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33266 (p : Pattern) (guard : d5843 p = 1) : d1794 p ≤ (2 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16120 p hg
    simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33265 p hg
    simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33267 (p : Pattern) (guard : d5843 p = 1) : d190 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12275 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33268 (p : Pattern) (guard : d5843 p = 1) : d1795 p ≤ (2 : Int) + d3461 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1795, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33266 p hg
    simpa only [d1795, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1795, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33267 p hg
    simpa only [d1795, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33269 (p : Pattern) (guard : d5843 p = 1) : d2011 p ≤ (2 : Int) + d7669 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2011, d7669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33264 p hg
    simpa only [d2011, d7669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2011, d7669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33268 p hg
    simpa only [d2011, d7669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33270 (p : Pattern) (guard : d5843 p = 1) : d2012 p ≤ (2 : Int) + d7670 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2012, d7670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33269 p hg
    simpa only [d2012, d7670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2012, d7670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33268 p hg
    simpa only [d2012, d7670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33271 (p : Pattern) (guard : d5843 p = 1) : d2897 p ≤ (2 : Int) + d7671 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2897, d7671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33264 p hg
    simpa only [d2897, d7671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2897, d7671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33270 p hg
    simpa only [d2897, d7671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33272 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (2 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33273 (p : Pattern) (guard : d5843 p = 1) : d1693 p ≤ (2 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15763 p hg
    simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33272 p hg
    simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33274 (p : Pattern) (guard : d5843 p = 1) : d34 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33275 (p : Pattern) (guard : d5843 p = 1) : d1694 p ≤ (2 : Int) + d3253 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1694, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33273 p hg
    simpa only [d1694, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1694, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33274 p hg
    simpa only [d1694, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33276 (p : Pattern) (guard : d5843 p = 1) : d1695 p ≤ (2 : Int) + d7672 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1695, d7672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33264 p hg
    simpa only [d1695, d7672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1695, d7672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33275 p hg
    simpa only [d1695, d7672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33277 (p : Pattern) (guard : d5843 p = 1) : d1696 p ≤ (2 : Int) + d7673 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1696, d7673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33276 p hg
    simpa only [d1696, d7673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1696, d7673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33275 p hg
    simpa only [d1696, d7673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33278 (p : Pattern) (guard : d5843 p = 1) : d1697 p ≤ (2 : Int) + d7674 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1697, d7674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33277 p hg
    simpa only [d1697, d7674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1697, d7674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1697, d7674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33279 (p : Pattern) (guard : d5843 p = 1) : d2898 p ≤ (2 : Int) + d7675 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2898, d7675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33271 p hg
    simpa only [d2898, d7675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2898, d7675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33278 p hg
    simpa only [d2898, d7675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33280 (p : Pattern) (guard : d5843 p = 1) : d2899 p ≤ (2 : Int) + d7676 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2899, d7676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33262 p hg
    simpa only [d2899, d7676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2899, d7676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33279 p hg
    simpa only [d2899, d7676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33281 (p : Pattern) (guard : d5843 p = 1) : d2900 p ≤ (2 : Int) + d7677 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2900, d7677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33262 p hg
    simpa only [d2900, d7677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2900, d7677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33280 p hg
    simpa only [d2900, d7677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33282 (p : Pattern) (guard : d5843 p = 1) : d9 p ≤ (2 : Int) + d9 p := by
  omega
theorem compare33283 (p : Pattern) (guard : d5843 p = 1) : d23 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1822 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33284 (p : Pattern) (guard : d5843 p = 1) : d24 p ≤ (2 : Int) + d3244 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d24, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33282 p hg
    simpa only [d24, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d24, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33283 p hg
    simpa only [d24, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33285 (p : Pattern) (guard : d5843 p = 1) : d356 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33283 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33286 (p : Pattern) (guard : d5843 p = 1) : d1802 p ≤ (2 : Int) + d7678 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1802, d7678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33284 p hg
    simpa only [d1802, d7678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1802, d7678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33285 p hg
    simpa only [d1802, d7678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33287 (p : Pattern) (guard : d5843 p = 1) : d1803 p ≤ (2 : Int) + d7679 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1803, d7679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33286 p hg
    simpa only [d1803, d7679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1803, d7679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33285 p hg
    simpa only [d1803, d7679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33288 (p : Pattern) (guard : d5843 p = 1) : d2901 p ≤ (2 : Int) + d7680 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2901, d7680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33284 p hg
    simpa only [d2901, d7680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2901, d7680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33287 p hg
    simpa only [d2901, d7680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33289 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (2 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33290 (p : Pattern) (guard : d5843 p = 1) : d1701 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15785 p hg
    simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33289 p hg
    simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33291 (p : Pattern) (guard : d5843 p = 1) : d39 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33292 (p : Pattern) (guard : d5843 p = 1) : d1702 p ≤ (2 : Int) + d3257 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1702, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33290 p hg
    simpa only [d1702, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1702, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33291 p hg
    simpa only [d1702, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33293 (p : Pattern) (guard : d5843 p = 1) : d1703 p ≤ (2 : Int) + d7681 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1703, d7681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33284 p hg
    simpa only [d1703, d7681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1703, d7681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33292 p hg
    simpa only [d1703, d7681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33294 (p : Pattern) (guard : d5843 p = 1) : d1704 p ≤ (2 : Int) + d7682 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1704, d7682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33293 p hg
    simpa only [d1704, d7682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1704, d7682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33292 p hg
    simpa only [d1704, d7682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33295 (p : Pattern) (guard : d5843 p = 1) : d1705 p ≤ (2 : Int) + d7683 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1705, d7683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33294 p hg
    simpa only [d1705, d7683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1705, d7683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1705, d7683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33296 (p : Pattern) (guard : d5843 p = 1) : d2902 p ≤ (2 : Int) + d7684 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2902, d7684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33288 p hg
    simpa only [d2902, d7684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2902, d7684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33295 p hg
    simpa only [d2902, d7684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33297 (p : Pattern) (guard : d5843 p = 1) : d2903 p ≤ (2 : Int) + d7685 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2903, d7685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33296 p hg
    simpa only [d2903, d7685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2903, d7685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2903, d7685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33298 (p : Pattern) (guard : d5843 p = 1) : d2904 p ≤ (2 : Int) + d7686 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2904, d7686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33280 p hg
    simpa only [d2904, d7686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2904, d7686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33297 p hg
    simpa only [d2904, d7686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33299 (p : Pattern) (guard : d5843 p = 1) : d2905 p ≤ (2 : Int) + d7687 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2905, d7687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33281 p hg
    simpa only [d2905, d7687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2905, d7687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33298 p hg
    simpa only [d2905, d7687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33300 (p : Pattern) (guard : d5843 p = 1) : d1775 p ≤ (2 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15755 p hg
    simpa only [d5843, d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33272 p hg
    simpa only [d5843, d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33301 (p : Pattern) (guard : d5843 p = 1) : d1776 p ≤ (2 : Int) + d3253 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1776, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33300 p hg
    simpa only [d1776, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1776, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33274 p hg
    simpa only [d1776, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33302 (p : Pattern) (guard : d5843 p = 1) : d1777 p ≤ (2 : Int) + d7688 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1777, d7688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33246 p hg
    simpa only [d1777, d7688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1777, d7688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33301 p hg
    simpa only [d1777, d7688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33303 (p : Pattern) (guard : d5843 p = 1) : d1785 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15776 p hg
    simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33289 p hg
    simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33304 (p : Pattern) (guard : d5843 p = 1) : d1786 p ≤ (2 : Int) + d3257 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1786, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33303 p hg
    simpa only [d1786, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1786, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33283 p hg
    simpa only [d1786, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33305 (p : Pattern) (guard : d5843 p = 1) : d1787 p ≤ (2 : Int) + d7689 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1787, d7689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33250 p hg
    simpa only [d1787, d7689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1787, d7689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33304 p hg
    simpa only [d1787, d7689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33306 (p : Pattern) (guard : d5843 p = 1) : d1788 p ≤ (2 : Int) + d7690 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1788, d7690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33302 p hg
    simpa only [d1788, d7690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1788, d7690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33305 p hg
    simpa only [d1788, d7690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33307 (p : Pattern) (guard : d5843 p = 1) : d2906 p ≤ (2 : Int) + d7691 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2906, d7691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33246 p hg
    simpa only [d2906, d7691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2906, d7691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33306 p hg
    simpa only [d2906, d7691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33308 (p : Pattern) (guard : d5843 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare33309 (p : Pattern) (guard : d5843 p = 1) : d31 p ≤ (2 : Int) + d3250 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d31, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33308 p hg
    simpa only [d31, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d31, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33256 p hg
    simpa only [d31, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33310 (p : Pattern) (guard : d5843 p = 1) : d1710 p ≤ (2 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16151 p hg
    simpa only [d5843, d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33265 p hg
    simpa only [d5843, d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33311 (p : Pattern) (guard : d5843 p = 1) : d1711 p ≤ (2 : Int) + d3461 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1711, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33310 p hg
    simpa only [d1711, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1711, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33267 p hg
    simpa only [d1711, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33312 (p : Pattern) (guard : d5843 p = 1) : d1712 p ≤ (2 : Int) + d7692 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1712, d7692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33309 p hg
    simpa only [d1712, d7692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1712, d7692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33311 p hg
    simpa only [d1712, d7692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33313 (p : Pattern) (guard : d5843 p = 1) : d1713 p ≤ (2 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24648 p hg
    simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33272 p hg
    simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33314 (p : Pattern) (guard : d5843 p = 1) : d1714 p ≤ (2 : Int) + d3253 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1714, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33313 p hg
    simpa only [d1714, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1714, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33274 p hg
    simpa only [d1714, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33315 (p : Pattern) (guard : d5843 p = 1) : d1715 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33256 p hg
    simpa only [d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33291 p hg
    simpa only [d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33316 (p : Pattern) (guard : d5843 p = 1) : d1716 p ≤ (2 : Int) + d7693 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1716, d7693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33314 p hg
    simpa only [d1716, d7693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1716, d7693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33315 p hg
    simpa only [d1716, d7693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33317 (p : Pattern) (guard : d5843 p = 1) : d1717 p ≤ (2 : Int) + d7694 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1717, d7694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33312 p hg
    simpa only [d1717, d7694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1717, d7694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33316 p hg
    simpa only [d1717, d7694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33318 (p : Pattern) (guard : d5843 p = 1) : d1718 p ≤ (2 : Int) + d7695 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1718, d7695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33317 p hg
    simpa only [d1718, d7695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1718, d7695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1718, d7695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33319 (p : Pattern) (guard : d5843 p = 1) : d2907 p ≤ (2 : Int) + d7696 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2907, d7696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33307 p hg
    simpa only [d2907, d7696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2907, d7696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33318 p hg
    simpa only [d2907, d7696, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
