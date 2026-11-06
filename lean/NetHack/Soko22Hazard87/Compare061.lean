import NetHack.Soko22Hazard87.Compare060
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare15250 (p : Pattern) (guard : d128316 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16605 p = 1 := by simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15249 p hg
    simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15251 (p : Pattern) (guard : d12961 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15235 p hg
    simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15252 (p : Pattern) (guard : d16574 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15207 p hg
    simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12961 p = 1 := by simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15251 p hg
    simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15253 (p : Pattern) (guard : d16575 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16575, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16575, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16574 p = 1 := by simpa only [d16575, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15252 p hg
    simpa only [d16575, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15254 (p : Pattern) (guard : d16576 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16576, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16576, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16575 p = 1 := by simpa only [d16576, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15253 p hg
    simpa only [d16576, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15255 (p : Pattern) (guard : d16577 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16576 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15254 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15256 (p : Pattern) (guard : d16578 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15221 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16577 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15255 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15257 (p : Pattern) (guard : d16579 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16578 p = 1 := by simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15256 p hg
    simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15258 (p : Pattern) (guard : d16580 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16579 p = 1 := by simpa only [d16580, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15257 p hg
    simpa only [d16580, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16580, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d16580, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15259 (p : Pattern) (guard : d16581 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16581, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d16581, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16580 p = 1 := by simpa only [d16581, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15258 p hg
    simpa only [d16581, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15260 (p : Pattern) (guard : d16582 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16581 p = 1 := by simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15259 p hg
    simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15261 (p : Pattern) (guard : d16583 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16582 p = 1 := by simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15260 p hg
    simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15262 (p : Pattern) (guard : d16584 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16583 p = 1 := by simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15261 p hg
    simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15263 (p : Pattern) (guard : d16610 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16584 p = 1 := by simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15262 p hg
    simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15264 (p : Pattern) (guard : d16611 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16610 p = 1 := by simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15263 p hg
    simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15265 (p : Pattern) (guard : d16612 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16611 p = 1 := by simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15264 p hg
    simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15266 (p : Pattern) (guard : d128317 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128316 p = 1 := by simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15250 p hg
    simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16612 p = 1 := by simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15265 p hg
    simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15267 (p : Pattern) (guard : d128325 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128317 p = 1 := by simpa only [d128325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15266 p hg
    simpa only [d128325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15268 (p : Pattern) (guard : d128326 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128325 p = 1 := by simpa only [d128326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15267 p hg
    simpa only [d128326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15269 (p : Pattern) (guard : d128327 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128327, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128327, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128326 p = 1 := by simpa only [d128327, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15268 p hg
    simpa only [d128327, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15270 (p : Pattern) (guard : d128328 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128327 p = 1 := by simpa only [d128328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15269 p hg
    simpa only [d128328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15271 (p : Pattern) (guard : d16467 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16462 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15244 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15272 (p : Pattern) (guard : d16468 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16467 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15271 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15273 (p : Pattern) (guard : d16469 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16468 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15272 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15274 (p : Pattern) (guard : d16480 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16469 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15273 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15275 (p : Pattern) (guard : d16629 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16480 p = 1 := by simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15274 p hg
    simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15276 (p : Pattern) (guard : d16630 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16629 p = 1 := by simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15275 p hg
    simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15277 (p : Pattern) (guard : d16631 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16630 p = 1 := by simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15276 p hg
    simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15278 (p : Pattern) (guard : d16632 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16631 p = 1 := by simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15277 p hg
    simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15279 (p : Pattern) (guard : d16633 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16632 p = 1 := by simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15278 p hg
    simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15280 (p : Pattern) (guard : d16643 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16643, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16643, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16633 p = 1 := by simpa only [d16643, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15279 p hg
    simpa only [d16643, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15281 (p : Pattern) (guard : d16644 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d16644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16643 p = 1 := by simpa only [d16644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15280 p hg
    simpa only [d16644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15282 (p : Pattern) (guard : d128329 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128328 p = 1 := by simpa only [d128329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15270 p hg
    simpa only [d128329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16644 p = 1 := by simpa only [d128329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15281 p hg
    simpa only [d128329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15283 (p : Pattern) (guard : d128330 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128329 p = 1 := by simpa only [d128330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15282 p hg
    simpa only [d128330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15284 (p : Pattern) (guard : d128331 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128330 p = 1 := by simpa only [d128331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15283 p hg
    simpa only [d128331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15285 (p : Pattern) (guard : d128332 p = 1) : d48359 p ≤ (1 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128324 p = 1 := by simpa only [d128332, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15169 p hg
    simpa only [d128332, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128331 p = 1 := by simpa only [d128332, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15284 p hg
    simpa only [d128332, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15286 (p : Pattern) (guard : d1378 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15287 (p : Pattern) (guard : d1379 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1378 p = 1 := by simpa only [d1379, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15286 p hg
    simpa only [d1379, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1379, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d1379, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15288 (p : Pattern) (guard : d16651 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15289 (p : Pattern) (guard : d16652 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16651 p = 1 := by simpa only [d16652, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15288 p hg
    simpa only [d16652, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16652, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d16652, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15290 (p : Pattern) (guard : d16653 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1379 p = 1 := by simpa only [d16653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15287 p hg
    simpa only [d16653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16652 p = 1 := by simpa only [d16653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15289 p hg
    simpa only [d16653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15291 (p : Pattern) (guard : d14989 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15292 (p : Pattern) (guard : d14990 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14989 p = 1 := by simpa only [d14990, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15291 p hg
    simpa only [d14990, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14990, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d14990, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15293 (p : Pattern) (guard : d14996 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15294 (p : Pattern) (guard : d14997 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14996 p = 1 := by simpa only [d14997, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15293 p hg
    simpa only [d14997, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14997, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d14997, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15295 (p : Pattern) (guard : d16654 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14990 p = 1 := by simpa only [d16654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15292 p hg
    simpa only [d16654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14997 p = 1 := by simpa only [d16654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15294 p hg
    simpa only [d16654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15296 (p : Pattern) (guard : d16655 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16653 p = 1 := by simpa only [d16655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15290 p hg
    simpa only [d16655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16654 p = 1 := by simpa only [d16655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15295 p hg
    simpa only [d16655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15297 (p : Pattern) (guard : d1382 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15298 (p : Pattern) (guard : d1383 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1382 p = 1 := by simpa only [d1383, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15297 p hg
    simpa only [d1383, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1383, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d1383, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15299 (p : Pattern) (guard : d16658 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15300 (p : Pattern) (guard : d16659 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16658 p = 1 := by simpa only [d16659, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15299 p hg
    simpa only [d16659, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16659, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d16659, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15301 (p : Pattern) (guard : d16660 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1383 p = 1 := by simpa only [d16660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15298 p hg
    simpa only [d16660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16659 p = 1 := by simpa only [d16660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15300 p hg
    simpa only [d16660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15302 (p : Pattern) (guard : d15006 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15303 (p : Pattern) (guard : d15007 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15006 p = 1 := by simpa only [d15007, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15302 p hg
    simpa only [d15007, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15007, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d15007, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15304 (p : Pattern) (guard : d16661 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14997 p = 1 := by simpa only [d16661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15294 p hg
    simpa only [d16661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15007 p = 1 := by simpa only [d16661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15303 p hg
    simpa only [d16661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15305 (p : Pattern) (guard : d16662 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16660 p = 1 := by simpa only [d16662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15301 p hg
    simpa only [d16662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16661 p = 1 := by simpa only [d16662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15304 p hg
    simpa only [d16662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15306 (p : Pattern) (guard : d16663 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16655 p = 1 := by simpa only [d16663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15296 p hg
    simpa only [d16663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16662 p = 1 := by simpa only [d16663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15305 p hg
    simpa only [d16663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15307 (p : Pattern) (guard : d16664 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16664, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d16664, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16663 p = 1 := by simpa only [d16664, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15306 p hg
    simpa only [d16664, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15308 (p : Pattern) (guard : d16665 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16665, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d16665, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16664 p = 1 := by simpa only [d16665, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15307 p hg
    simpa only [d16665, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15309 (p : Pattern) (guard : d13162 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15310 (p : Pattern) (guard : d13163 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13162 p = 1 := by simpa only [d13163, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15309 p hg
    simpa only [d13163, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13163, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d13163, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15311 (p : Pattern) (guard : d16666 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13163 p = 1 := by simpa only [d16666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15310 p hg
    simpa only [d16666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15007 p = 1 := by simpa only [d16666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15303 p hg
    simpa only [d16666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15312 (p : Pattern) (guard : d15008 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15007 p = 1 := by simpa only [d15008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15303 p hg
    simpa only [d15008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d15008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15313 (p : Pattern) (guard : d16667 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16666 p = 1 := by simpa only [d16667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15311 p hg
    simpa only [d16667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15008 p = 1 := by simpa only [d16667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15312 p hg
    simpa only [d16667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15314 (p : Pattern) (guard : d16668 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16662 p = 1 := by simpa only [d16668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15305 p hg
    simpa only [d16668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16667 p = 1 := by simpa only [d16668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15313 p hg
    simpa only [d16668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15315 (p : Pattern) (guard : d16669 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16669, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d16669, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16668 p = 1 := by simpa only [d16669, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15314 p hg
    simpa only [d16669, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15316 (p : Pattern) (guard : d16670 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16670, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d16670, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16669 p = 1 := by simpa only [d16670, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15315 p hg
    simpa only [d16670, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15317 (p : Pattern) (guard : d16671 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16665 p = 1 := by simpa only [d16671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15308 p hg
    simpa only [d16671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16670 p = 1 := by simpa only [d16671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15316 p hg
    simpa only [d16671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15318 (p : Pattern) (guard : d1387 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15319 (p : Pattern) (guard : d1388 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1387 p = 1 := by simpa only [d1388, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15318 p hg
    simpa only [d1388, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1388, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d1388, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15320 (p : Pattern) (guard : d1393 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15321 (p : Pattern) (guard : d1394 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1393 p = 1 := by simpa only [d1394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15320 p hg
    simpa only [d1394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d1394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15322 (p : Pattern) (guard : d1395 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1388 p = 1 := by simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15319 p hg
    simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1394 p = 1 := by simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15321 p hg
    simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15323 (p : Pattern) (guard : d16672 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1395 p = 1 := by simpa only [d16672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15322 p hg
    simpa only [d16672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15008 p = 1 := by simpa only [d16672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15312 p hg
    simpa only [d16672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15324 (p : Pattern) (guard : d16673 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16662 p = 1 := by simpa only [d16673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15305 p hg
    simpa only [d16673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16672 p = 1 := by simpa only [d16673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15323 p hg
    simpa only [d16673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15325 (p : Pattern) (guard : d16674 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16674, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d16674, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16673 p = 1 := by simpa only [d16674, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15324 p hg
    simpa only [d16674, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15326 (p : Pattern) (guard : d16675 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16675, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d16675, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16674 p = 1 := by simpa only [d16675, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15325 p hg
    simpa only [d16675, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15327 (p : Pattern) (guard : d6352 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15328 (p : Pattern) (guard : d6353 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6352 p = 1 := by simpa only [d6353, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15327 p hg
    simpa only [d6353, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6353, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d6353, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15329 (p : Pattern) (guard : d6354 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d6353 p = 1 := by simpa only [d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15328 p hg
    simpa only [d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15330 (p : Pattern) (guard : d15021 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15331 (p : Pattern) (guard : d15022 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15021 p = 1 := by simpa only [d15022, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15330 p hg
    simpa only [d15022, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15022, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d15022, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15332 (p : Pattern) (guard : d15023 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15022 p = 1 := by simpa only [d15023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15331 p hg
    simpa only [d15023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d15023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15333 (p : Pattern) (guard : d15024 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d6354 p = 1 := by simpa only [d15024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15329 p hg
    simpa only [d15024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15023 p = 1 := by simpa only [d15024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15332 p hg
    simpa only [d15024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15334 (p : Pattern) (guard : d16676 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16672 p = 1 := by simpa only [d16676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15323 p hg
    simpa only [d16676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15024 p = 1 := by simpa only [d16676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15333 p hg
    simpa only [d16676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15335 (p : Pattern) (guard : d16677 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16677, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d16677, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16676 p = 1 := by simpa only [d16677, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15334 p hg
    simpa only [d16677, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15336 (p : Pattern) (guard : d16678 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16678, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d16678, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16677 p = 1 := by simpa only [d16678, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15335 p hg
    simpa only [d16678, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15337 (p : Pattern) (guard : d16679 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16675 p = 1 := by simpa only [d16679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15326 p hg
    simpa only [d16679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16678 p = 1 := by simpa only [d16679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15336 p hg
    simpa only [d16679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15338 (p : Pattern) (guard : d16680 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16671 p = 1 := by simpa only [d16680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15317 p hg
    simpa only [d16680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16679 p = 1 := by simpa only [d16680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15337 p hg
    simpa only [d16680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15339 (p : Pattern) (guard : d16681 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16680 p = 1 := by simpa only [d16681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15338 p hg
    simpa only [d16681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15340 (p : Pattern) (guard : d16682 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16681 p = 1 := by simpa only [d16682, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15339 p hg
    simpa only [d16682, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16682, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d16682, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15341 (p : Pattern) (guard : d16683 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16683, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16683, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16682 p = 1 := by simpa only [d16683, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15340 p hg
    simpa only [d16683, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15342 (p : Pattern) (guard : d16684 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16678 p = 1 := by simpa only [d16684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15336 p hg
    simpa only [d16684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15343 (p : Pattern) (guard : d16685 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16679 p = 1 := by simpa only [d16685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15337 p hg
    simpa only [d16685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16684 p = 1 := by simpa only [d16685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15342 p hg
    simpa only [d16685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15344 (p : Pattern) (guard : d16686 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16685 p = 1 := by simpa only [d16686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15343 p hg
    simpa only [d16686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15345 (p : Pattern) (guard : d16687 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16686 p = 1 := by simpa only [d16687, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15344 p hg
    simpa only [d16687, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16687, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d16687, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15346 (p : Pattern) (guard : d16688 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16688, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16688, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16687 p = 1 := by simpa only [d16688, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15345 p hg
    simpa only [d16688, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15347 (p : Pattern) (guard : d16689 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16683 p = 1 := by simpa only [d16689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15341 p hg
    simpa only [d16689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16688 p = 1 := by simpa only [d16689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15346 p hg
    simpa only [d16689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15348 (p : Pattern) (guard : d16690 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16689 p = 1 := by simpa only [d16690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15347 p hg
    simpa only [d16690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15349 (p : Pattern) (guard : d16691 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16690 p = 1 := by simpa only [d16691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15348 p hg
    simpa only [d16691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15350 (p : Pattern) (guard : d16692 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16691 p = 1 := by simpa only [d16692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15349 p hg
    simpa only [d16692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15351 (p : Pattern) (guard : d1400 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1394 p = 1 := by simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15321 p hg
    simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15352 (p : Pattern) (guard : d15042 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1400 p = 1 := by simpa only [d15042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15351 p hg
    simpa only [d15042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15023 p = 1 := by simpa only [d15042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15332 p hg
    simpa only [d15042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15353 (p : Pattern) (guard : d16693 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16672 p = 1 := by simpa only [d16693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15323 p hg
    simpa only [d16693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15042 p = 1 := by simpa only [d16693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15352 p hg
    simpa only [d16693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15354 (p : Pattern) (guard : d16694 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16694, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d16694, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16693 p = 1 := by simpa only [d16694, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15353 p hg
    simpa only [d16694, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15355 (p : Pattern) (guard : d16695 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16695, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d16695, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16694 p = 1 := by simpa only [d16695, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15354 p hg
    simpa only [d16695, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15356 (p : Pattern) (guard : d16696 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16695 p = 1 := by simpa only [d16696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15355 p hg
    simpa only [d16696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15357 (p : Pattern) (guard : d16697 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16696 p = 1 := by simpa only [d16697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15356 p hg
    simpa only [d16697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15358 (p : Pattern) (guard : d16698 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16697 p = 1 := by simpa only [d16698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15357 p hg
    simpa only [d16698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15359 (p : Pattern) (guard : d16699 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16698 p = 1 := by simpa only [d16699, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15358 p hg
    simpa only [d16699, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16699, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d16699, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15360 (p : Pattern) (guard : d16700 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16700, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16700, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16699 p = 1 := by simpa only [d16700, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15359 p hg
    simpa only [d16700, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15361 (p : Pattern) (guard : d16701 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16688 p = 1 := by simpa only [d16701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15346 p hg
    simpa only [d16701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16700 p = 1 := by simpa only [d16701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15360 p hg
    simpa only [d16701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15362 (p : Pattern) (guard : d16702 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16701 p = 1 := by simpa only [d16702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15361 p hg
    simpa only [d16702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15363 (p : Pattern) (guard : d16703 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16702 p = 1 := by simpa only [d16703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15362 p hg
    simpa only [d16703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15364 (p : Pattern) (guard : d16704 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16703 p = 1 := by simpa only [d16704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15363 p hg
    simpa only [d16704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15365 (p : Pattern) (guard : d16705 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16692 p = 1 := by simpa only [d16705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15350 p hg
    simpa only [d16705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16704 p = 1 := by simpa only [d16705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15364 p hg
    simpa only [d16705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15366 (p : Pattern) (guard : d128333 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16705 p = 1 := by simpa only [d128333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15365 p hg
    simpa only [d128333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15367 (p : Pattern) (guard : d13190 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1400 p = 1 := by simpa only [d13190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15351 p hg
    simpa only [d13190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d13190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15368 (p : Pattern) (guard : d16743 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16672 p = 1 := by simpa only [d16743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15323 p hg
    simpa only [d16743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13190 p = 1 := by simpa only [d16743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15367 p hg
    simpa only [d16743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15369 (p : Pattern) (guard : d16744 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16744, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d16744, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16743 p = 1 := by simpa only [d16744, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15368 p hg
    simpa only [d16744, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15370 (p : Pattern) (guard : d16745 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16745, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d16745, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16744 p = 1 := by simpa only [d16745, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15369 p hg
    simpa only [d16745, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15371 (p : Pattern) (guard : d16746 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16745 p = 1 := by simpa only [d16746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15370 p hg
    simpa only [d16746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15372 (p : Pattern) (guard : d16747 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16679 p = 1 := by simpa only [d16747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15337 p hg
    simpa only [d16747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16746 p = 1 := by simpa only [d16747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15371 p hg
    simpa only [d16747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15373 (p : Pattern) (guard : d16748 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16747 p = 1 := by simpa only [d16748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15372 p hg
    simpa only [d16748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15374 (p : Pattern) (guard : d16749 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16748 p = 1 := by simpa only [d16749, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15373 p hg
    simpa only [d16749, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16749, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d16749, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15375 (p : Pattern) (guard : d16750 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16750, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16750, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16749 p = 1 := by simpa only [d16750, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15374 p hg
    simpa only [d16750, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15376 (p : Pattern) (guard : d16751 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16750 p = 1 := by simpa only [d16751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15375 p hg
    simpa only [d16751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15377 (p : Pattern) (guard : d16752 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16751 p = 1 := by simpa only [d16752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15376 p hg
    simpa only [d16752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15378 (p : Pattern) (guard : d16753 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16752 p = 1 := by simpa only [d16753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15377 p hg
    simpa only [d16753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15379 (p : Pattern) (guard : d16754 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16753 p = 1 := by simpa only [d16754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15378 p hg
    simpa only [d16754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15380 (p : Pattern) (guard : d16755 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16754 p = 1 := by simpa only [d16755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15379 p hg
    simpa only [d16755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15381 (p : Pattern) (guard : d16756 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16755 p = 1 := by simpa only [d16756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15380 p hg
    simpa only [d16756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15382 (p : Pattern) (guard : d128334 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128333 p = 1 := by simpa only [d128334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15366 p hg
    simpa only [d128334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16756 p = 1 := by simpa only [d128334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15381 p hg
    simpa only [d128334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15383 (p : Pattern) (guard : d128335 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128334 p = 1 := by simpa only [d128335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15382 p hg
    simpa only [d128335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15384 (p : Pattern) (guard : d128336 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128335 p = 1 := by simpa only [d128336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15383 p hg
    simpa only [d128336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15385 (p : Pattern) (guard : d128337 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128337, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128337, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128336 p = 1 := by simpa only [d128337, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15384 p hg
    simpa only [d128337, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15386 (p : Pattern) (guard : d128338 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128337 p = 1 := by simpa only [d128338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15385 p hg
    simpa only [d128338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15387 (p : Pattern) (guard : d16762 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16700 p = 1 := by simpa only [d16762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15360 p hg
    simpa only [d16762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15388 (p : Pattern) (guard : d16763 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16762 p = 1 := by simpa only [d16763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15387 p hg
    simpa only [d16763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15389 (p : Pattern) (guard : d16764 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16763 p = 1 := by simpa only [d16764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15388 p hg
    simpa only [d16764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15390 (p : Pattern) (guard : d16765 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16764 p = 1 := by simpa only [d16765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15389 p hg
    simpa only [d16765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15391 (p : Pattern) (guard : d16766 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16765 p = 1 := by simpa only [d16766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15390 p hg
    simpa only [d16766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15392 (p : Pattern) (guard : d16767 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16766 p = 1 := by simpa only [d16767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15391 p hg
    simpa only [d16767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15393 (p : Pattern) (guard : d16768 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16767 p = 1 := by simpa only [d16768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15392 p hg
    simpa only [d16768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15394 (p : Pattern) (guard : d16769 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16768 p = 1 := by simpa only [d16769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15393 p hg
    simpa only [d16769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15395 (p : Pattern) (guard : d16770 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16769 p = 1 := by simpa only [d16770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15394 p hg
    simpa only [d16770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15396 (p : Pattern) (guard : d16771 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16771, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16771, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16770 p = 1 := by simpa only [d16771, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15395 p hg
    simpa only [d16771, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15397 (p : Pattern) (guard : d16772 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d16772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16771 p = 1 := by simpa only [d16772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15396 p hg
    simpa only [d16772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15398 (p : Pattern) (guard : d128339 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128338 p = 1 := by simpa only [d128339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15386 p hg
    simpa only [d128339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16772 p = 1 := by simpa only [d128339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15397 p hg
    simpa only [d128339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15399 (p : Pattern) (guard : d128340 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128339 p = 1 := by simpa only [d128340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15398 p hg
    simpa only [d128340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15400 (p : Pattern) (guard : d128341 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128340 p = 1 := by simpa only [d128341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15399 p hg
    simpa only [d128341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15401 (p : Pattern) (guard : d128342 p = 1) : d48387 p ≤ (1 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128341 p = 1 := by simpa only [d128342, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15400 p hg
    simpa only [d128342, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128342, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13796 p hg
    simpa only [d128342, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15402 (p : Pattern) (guard : d128343 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d128332 p = 1 := by simpa only [d128343, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15285 p hg
    simpa only [d128343, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128342 p = 1 := by simpa only [d128343, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15401 p hg
    simpa only [d128343, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15403 (p : Pattern) (guard : d128344 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128343 p = 1 := by simpa only [d128344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15402 p hg
    simpa only [d128344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15404 (p : Pattern) (guard : d128345 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128344 p = 1 := by simpa only [d128345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15403 p hg
    simpa only [d128345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15405 (p : Pattern) (guard : d128346 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128345 p = 1 := by simpa only [d128346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15404 p hg
    simpa only [d128346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15406 (p : Pattern) (guard : d128347 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128346 p = 1 := by simpa only [d128347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15405 p hg
    simpa only [d128347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15407 (p : Pattern) (guard : d128348 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128347 p = 1 := by simpa only [d128348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15406 p hg
    simpa only [d128348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15408 (p : Pattern) (guard : d128349 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128348 p = 1 := by simpa only [d128349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15407 p hg
    simpa only [d128349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15409 (p : Pattern) (guard : d128350 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128349 p = 1 := by simpa only [d128350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15408 p hg
    simpa only [d128350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15410 (p : Pattern) (guard : d128351 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128350 p = 1 := by simpa only [d128351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15409 p hg
    simpa only [d128351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15411 (p : Pattern) (guard : d128352 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d128310 p = 1 := by simpa only [d128352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14892 p hg
    simpa only [d128352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128351 p = 1 := by simpa only [d128352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15410 p hg
    simpa only [d128352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15412 (p : Pattern) (guard : d1557 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15413 (p : Pattern) (guard : d1558 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15412 p hg
    simpa only [d1558, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1558, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15414 (p : Pattern) (guard : d16787 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15415 (p : Pattern) (guard : d16788 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16787 p = 1 := by simpa only [d16788, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15414 p hg
    simpa only [d16788, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16788, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d16788, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15416 (p : Pattern) (guard : d16789 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15413 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16788 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15415 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15417 (p : Pattern) (guard : d15151 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15418 (p : Pattern) (guard : d15152 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15151 p = 1 := by simpa only [d15152, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15417 p hg
    simpa only [d15152, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15152, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d15152, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15419 (p : Pattern) (guard : d15156 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15420 (p : Pattern) (guard : d15157 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15156 p = 1 := by simpa only [d15157, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15419 p hg
    simpa only [d15157, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15157, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d15157, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15421 (p : Pattern) (guard : d16790 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15152 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15418 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15420 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15422 (p : Pattern) (guard : d16791 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16789 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15416 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16790 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15421 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15423 (p : Pattern) (guard : d1572 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15424 (p : Pattern) (guard : d1573 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15423 p hg
    simpa only [d1573, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1573, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15425 (p : Pattern) (guard : d16792 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15426 (p : Pattern) (guard : d16793 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16792 p = 1 := by simpa only [d16793, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15425 p hg
    simpa only [d16793, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16793, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d16793, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15427 (p : Pattern) (guard : d16794 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16793 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15426 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15428 (p : Pattern) (guard : d15158 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15157 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15420 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15429 (p : Pattern) (guard : d16795 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16794 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15427 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15428 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15430 (p : Pattern) (guard : d16796 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15422 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16795 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15429 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15431 (p : Pattern) (guard : d16797 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16797, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16797, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16796 p = 1 := by simpa only [d16797, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15430 p hg
    simpa only [d16797, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15432 (p : Pattern) (guard : d16798 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16798, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15431 p hg
    simpa only [d16798, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15433 (p : Pattern) (guard : d5136 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15434 (p : Pattern) (guard : d5137 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d5137, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d5137, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15435 (p : Pattern) (guard : d5138 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15434 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15436 (p : Pattern) (guard : d15163 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15437 (p : Pattern) (guard : d15164 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15163 p = 1 := by simpa only [d15164, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15436 p hg
    simpa only [d15164, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15164, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d15164, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15438 (p : Pattern) (guard : d15165 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15164 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15437 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15439 (p : Pattern) (guard : d15166 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15435 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15438 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15440 (p : Pattern) (guard : d16799 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15429 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15166 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15439 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15441 (p : Pattern) (guard : d16800 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16800, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16800, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16799 p = 1 := by simpa only [d16800, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15440 p hg
    simpa only [d16800, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15442 (p : Pattern) (guard : d16801 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16801, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15441 p hg
    simpa only [d16801, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15443 (p : Pattern) (guard : d16802 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15432 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15442 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15444 (p : Pattern) (guard : d1584 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15445 (p : Pattern) (guard : d1585 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15444 p hg
    simpa only [d1585, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1585, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15446 (p : Pattern) (guard : d1588 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15445 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15447 (p : Pattern) (guard : d15171 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15446 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15438 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15448 (p : Pattern) (guard : d16803 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15429 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15171 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15447 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15449 (p : Pattern) (guard : d16804 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16804, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16804, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16803 p = 1 := by simpa only [d16804, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15448 p hg
    simpa only [d16804, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15450 (p : Pattern) (guard : d16805 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16805, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15449 p hg
    simpa only [d16805, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15451 (p : Pattern) (guard : d16806 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15450 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15452 (p : Pattern) (guard : d16807 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15443 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16806 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15451 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15453 (p : Pattern) (guard : d16808 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16807 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15452 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15454 (p : Pattern) (guard : d16809 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16808 p = 1 := by simpa only [d16809, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15453 p hg
    simpa only [d16809, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16809, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16809, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15455 (p : Pattern) (guard : d16810 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16810, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16810, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16809 p = 1 := by simpa only [d16810, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15454 p hg
    simpa only [d16810, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15456 (p : Pattern) (guard : d16811 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15451 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15457 (p : Pattern) (guard : d16812 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15456 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15458 (p : Pattern) (guard : d16813 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16812 p = 1 := by simpa only [d16813, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15457 p hg
    simpa only [d16813, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16813, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16813, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15459 (p : Pattern) (guard : d16814 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16814, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16814, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16813 p = 1 := by simpa only [d16814, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15458 p hg
    simpa only [d16814, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15460 (p : Pattern) (guard : d16815 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16810 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15455 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15459 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15461 (p : Pattern) (guard : d16816 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16815 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15460 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15462 (p : Pattern) (guard : d16817 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16816 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15461 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15463 (p : Pattern) (guard : d16818 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16817 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15462 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15464 (p : Pattern) (guard : d16819 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16814 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15459 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15465 (p : Pattern) (guard : d16820 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16819 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15464 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15466 (p : Pattern) (guard : d16821 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16820 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15465 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15467 (p : Pattern) (guard : d16822 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16821 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15466 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15468 (p : Pattern) (guard : d16823 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16818 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15463 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16822 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15469 (p : Pattern) (guard : d16824 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16823 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15468 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15470 (p : Pattern) (guard : d16825 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16824 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15469 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15471 (p : Pattern) (guard : d16826 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16825 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15470 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15472 (p : Pattern) (guard : d16827 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16826 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15471 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15473 (p : Pattern) (guard : d16828 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16827 p = 1 := by simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15472 p hg
    simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15474 (p : Pattern) (guard : d16829 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d16829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16828 p = 1 := by simpa only [d16829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15473 p hg
    simpa only [d16829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15475 (p : Pattern) (guard : d16830 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16829 p = 1 := by simpa only [d16830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15474 p hg
    simpa only [d16830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d16830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15476 (p : Pattern) (guard : d16798 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16798, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15431 p hg
    simpa only [d16798, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15477 (p : Pattern) (guard : d16801 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16801, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15441 p hg
    simpa only [d16801, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15478 (p : Pattern) (guard : d16802 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15476 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15477 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15479 (p : Pattern) (guard : d16805 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16805, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15449 p hg
    simpa only [d16805, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15480 (p : Pattern) (guard : d16806 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15479 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15481 (p : Pattern) (guard : d16807 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15478 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16806 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15480 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15482 (p : Pattern) (guard : d16808 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16807 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15481 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15483 (p : Pattern) (guard : d16809 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16808 p = 1 := by simpa only [d16809, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15482 p hg
    simpa only [d16809, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16809, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16809, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15484 (p : Pattern) (guard : d16810 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16810, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16810, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16809 p = 1 := by simpa only [d16810, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15483 p hg
    simpa only [d16810, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15485 (p : Pattern) (guard : d16811 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15480 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15486 (p : Pattern) (guard : d16812 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15485 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15487 (p : Pattern) (guard : d16813 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16812 p = 1 := by simpa only [d16813, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15486 p hg
    simpa only [d16813, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16813, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16813, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15488 (p : Pattern) (guard : d16814 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16814, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16814, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16813 p = 1 := by simpa only [d16814, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15487 p hg
    simpa only [d16814, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15489 (p : Pattern) (guard : d16815 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16810 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15484 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15488 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15490 (p : Pattern) (guard : d16816 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16815 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15489 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15491 (p : Pattern) (guard : d16817 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16816 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15490 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15492 (p : Pattern) (guard : d16818 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16817 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15491 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15493 (p : Pattern) (guard : d16819 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16814 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15488 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15494 (p : Pattern) (guard : d16820 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16819 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15493 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15495 (p : Pattern) (guard : d16821 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16820 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15494 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15496 (p : Pattern) (guard : d16822 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16821 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15495 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15497 (p : Pattern) (guard : d16823 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16818 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15492 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16822 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15496 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15498 (p : Pattern) (guard : d16824 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16823 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15497 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15499 (p : Pattern) (guard : d16825 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16824 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15498 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
